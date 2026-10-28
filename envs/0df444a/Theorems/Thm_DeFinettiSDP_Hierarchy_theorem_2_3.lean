-- Prove2me | Theorems.Thm_DeFinettiSDP_Hierarchy_theorem_2_3
-- name    : DeFinettiSDP.Hierarchy.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:30.020997+00:00
-- url     : https://prove2.me/theorems/af5b5baa-c54f-4f4b-8be8-90e838ddfcda
-- title:
--   Theorem 2.3, p. 7 — de Finetti with linear constraints: ‖ρ_{AB} − Σ pᵢσⁱ⊗ωⁱ‖₁ ≤ min{f(A,B), f(B|·)}·√((2 ln 2) log d_A/n)
-- statement:
--   Let $\rho_{AB_1^n}$ be a quantum state on $A\otimes B_1\cdots B_n$ ($n\ge1$, $\dim A=d_A$, each $B_i$ a copy of $B$), $\Lambda_{A\to C_A}$, $\Gamma_{B\to C_B}$ linear maps, and $X_{C_A}$, $Y_{C_B}$ matrices such that
--
--   1. $\mathcal U^\pi_{B_1^n}(\rho_{AB_1^n})=\rho_{AB_1^n}$ for every $\pi\in\mathfrak S_n$ (symmetric with respect to $A$);
--   2. $\Lambda_{A\to C_A}(\rho_{AB_1^n})=X_{C_A}\otimes\rho_{B_1^n}$ (linear constraint on $A$);
--   3. $\Gamma_{B_n\to C_B}(\rho_{B_1^n})=\rho_{B_1^{n-1}}\otimes Y_{C_B}$ (linear constraint on $B$).
--
--   Then there are a finite probability distribution $\{p_i\}_{i\in I}$ and quantum states $\sigma^i_A$, $\omega^i_B$ with $\Lambda_{A\to C_A}(\sigma^i_A)=X_{C_A}$ and $\Gamma_{B\to C_B}(\omega^i_B)=Y_{C_B}$ for every $i$, such that
--
--   $$\Big\|\rho_{AB}-\sum_{i\in I}p_i\,\sigma^i_A\otimes\omega^i_B\Big\|_1\ \le\ \min\{f(A,B),f(B|\cdot)\}\sqrt{\frac{(2\ln2)\log d_A}{n}},$$
--
--   where $\rho_{AB}=\mathrm{Tr}_{B_2^n}[\rho_{AB_1^n}]$, $\log$ is base 2, and $f(A,B)$, $f(B|\cdot)$ are the minimal distortions (9) and (10).
--
--   The constraints of the extension pass to the approximating mixture: this is what makes the SDP hierarchy for constrained bilinear programs converge to the right value.
--
--   **Formalization Note** The page's $n$ is `n + 1` here. The bound is stated in $[0,\infty]$ because $f(A,B)$ and $f(B|\cdot)$ are $[0,\infty]$-valued; at $d_A=1$ the right side is $0$ (and the claim is exact decomposability). The page's closing sentence ("we can, e.g., take $f(A,B)\le18\sqrt{d_Ad_B}$ or $f(B|\cdot)\le\sqrt{18d_B^3}$") cites [12], [13] and is not formalized here; the mission uses $f(B|\cdot)\le d_B^2(d_B+1)$ instead.
-- source:
--   Berta, Borderi, Fawzi & Scholz, arXiv:1810.12197v3, Theorem 2.3, p. 7

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_DeFinettiSDP_Hierarchy_Systems
import Definitions.Def_DeFinettiSDP_Hierarchy_Distortion
open Matrix
open scoped Kronecker ComplexOrder

namespace DeFinettiSDP.Hierarchy

/-- **Theorem 2.3** (arXiv:1810.12197v3, p. 7), de Finetti theorem with linear constraints. Let `ρ`
be a state on `A ⊗ B₁ ⋯ B_{n+1}` (the page's `n` is `n + 1` here), `Λ`, `Γ` linear maps and `X`,
`Y` matrices with `ρ` symmetric with respect to `A`, `(Λ ⊗ I)(ρ) = X ⊗ ρ_{B₁⋯B_{n+1}}` and
`(I ⊗ Γ_{B_{n+1}})(ρ_{B₁⋯B_{n+1}}) = ρ_{B₁⋯B_n} ⊗ Y`. Then there are a probability distribution `p`
and states `σ^i` on `A`, `ω^i` on `B` with `Λ(σ^i) = X`, `Γ(ω^i) = Y`, such that
`‖ρ_{AB₁} − ∑_i p_i σ^i ⊗ ω^i‖₁ ≤ min{f(A,B), f(B|·)} √((2 ln 2) log₂ d_A / (n + 1))`. -/
theorem theorem_2_3 {dA dB cA cB : ℕ} (n : ℕ)
    (ρ : Matrix (Fin dA × (Fin (n + 1) → Fin dB)) (Fin dA × (Fin (n + 1) → Fin dB)) ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ)
    (Λ : Matrix (Fin dA) (Fin dA) ℂ →ₗ[ℂ] Matrix (Fin cA) (Fin cA) ℂ)
    (Γ : Matrix (Fin dB) (Fin dB) ℂ →ₗ[ℂ] Matrix (Fin cB) (Fin cB) ℂ)
    (X : Matrix (Fin cA) (Fin cA) ℂ) (Y : Matrix (Fin cB) (Fin cB) ℂ)
    (hsym : ∀ π : Equiv.Perm (Fin (n + 1)), permB π ρ = ρ)
    (hΛ : applyFirst Λ ρ = X ⊗ₖ trA ρ)
    (hΓ : applyLast Γ (splitLast (trA ρ)) = trLast (trA ρ) ⊗ₖ Y) :
    ∃ (N : ℕ) (p : Fin N → ℝ) (σ : Fin N → Matrix (Fin dA) (Fin dA) ℂ)
      (ω : Fin N → Matrix (Fin dB) (Fin dB) ℂ),
      (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1 ∧
      (∀ i, WildeQIT.IsDensityOperator (σ i) ∧ Λ (σ i) = X) ∧
      (∀ i, WildeQIT.IsDensityOperator (ω i) ∧ Γ (ω i) = Y) ∧
      ENNReal.ofReal (WildeQIT.traceNorm (keepAB1 ρ - ∑ i, (p i : ℂ) • (σ i ⊗ₖ ω i))) ≤
        min (fAB dA dB) (fBside dB) *
          ENNReal.ofReal (Real.sqrt (2 * Real.log 2 * Real.logb 2 (dA : ℝ) / ((n : ℝ) + 1))) := by sorry

end DeFinettiSDP.Hierarchy
