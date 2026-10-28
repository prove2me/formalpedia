-- Prove2me | Theorems.Thm_DeFinettiSDP_Hierarchy_conditional_constraints
-- name    : DeFinettiSDP.Hierarchy.conditional_constraints
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:05.191819+00:00
-- url     : https://prove2.me/theorems/08c23dc2-6ab9-4cfd-84f2-bd3b9c2d23ea
-- title:
--   Proof of Theorem 2.3, p. 8 — the conditional states satisfy Λ(ρ_{A|z^m_1}) = X and Γ(ρ_{B_{m+1}|z^m_1}) = Y
-- statement:
--   Let $\rho_{AB_1^{n}}$ be a state on $A\otimes B_1\cdots B_n$ ($n\ge1$), $\Lambda_{A\to C_A}$, $\Gamma_{B\to C_B}$ linear maps and $X_{C_A}$, $Y_{C_B}$ matrices such that
--
--   1. $\mathcal U^\pi_{B_1^n}(\rho_{AB_1^n})=\rho_{AB_1^n}$ for every $\pi\in\mathfrak S_n$;
--   2. $\Lambda_{A\to C_A}(\rho_{AB_1^n})=X_{C_A}\otimes\rho_{B_1^n}$;
--   3. $\Gamma_{B_n\to C_B}(\rho_{B_1^n})=\rho_{B_1^{n-1}}\otimes Y_{C_B}$.
--
--   Let $\{M_z\}$ be a measurement on $B$, $0\le m<n$, and $z_1^m=(z_1,\dots,z_m)$ an outcome string of positive probability $p(z_1^m)=\mathrm{Tr}[(\mathbb 1_A\otimes M_{z_1}\otimes\cdots\otimes M_{z_m})\rho_{AB_1^m}]$ when $B_1,\dots,B_m$ are measured. Then the conditional states satisfy the linear constraints exactly:
--
--   $$\Lambda_{A\to C_A}\big(\rho_{A|z_1^m}\big)=X_{C_A},\qquad \Gamma_{B\to C_B}\big(\rho_{B_{m+1}|z_1^m}\big)=Y_{C_B}.$$
--
--   This is why the de Finetti approximant of Theorem 2.3 is a mixture of *feasible* product states.
--
--   **Formalization Note** The page's $n$ is `n + 1` here, and $m$ ranges over $\{0,\dots,n\}$ (`m : Fin (n + 1)`). The conditional states are defined by explicit partial traces after measuring $B_1,\dots,B_m$ (`condA`, `condB`). "For any $z_1^m$" on the page is read as any outcome string of positive probability, since the conditional states are undefined otherwise; this is the added hypothesis `0 < pMeas …`.
-- source:
--   Berta, Borderi, Fawzi & Scholz, arXiv:1810.12197v3, proof of Theorem 2.3, p. 8, the two displays after "It now remains to show"

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_DeFinettiSDP_Hierarchy_Systems
import Definitions.Def_DeFinettiSDP_Hierarchy_Conditional
open Matrix
open scoped Kronecker ComplexOrder

namespace DeFinettiSDP.Hierarchy

/-- **Linear constraints of the conditional states** (arXiv:1810.12197v3, proof of Theorem 2.3,
p. 8). Let `ρ` on `A ⊗ B₁ ⋯ B_{n+1}` satisfy the hypotheses of Theorem 2.3 (state, symmetric
in the `B`'s with respect to `A`, `(Λ ⊗ I)(ρ) = X ⊗ ρ_{B₁⋯B_{n+1}}`,
`(I ⊗ Γ_{B_{n+1}})(ρ_{B₁⋯B_{n+1}}) = ρ_{B₁⋯B_n} ⊗ Y`), and let `M` be a measurement on `B`. Measure
`B₁, …, B_m` (`m ≤ n`) with `M`; for every outcome string `w` of positive probability the
conditional states satisfy `Λ(ρ_{A|w}) = X` and `Γ(ρ_{B_{m+1}|w}) = Y`. -/
theorem conditional_constraints {dA dB cA cB t n : ℕ}
    (ρ : Matrix (Fin dA × (Fin (n + 1) → Fin dB)) (Fin dA × (Fin (n + 1) → Fin dB)) ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ)
    (Λ : Matrix (Fin dA) (Fin dA) ℂ →ₗ[ℂ] Matrix (Fin cA) (Fin cA) ℂ)
    (Γ : Matrix (Fin dB) (Fin dB) ℂ →ₗ[ℂ] Matrix (Fin cB) (Fin cB) ℂ)
    (X : Matrix (Fin cA) (Fin cA) ℂ) (Y : Matrix (Fin cB) (Fin cB) ℂ)
    (hsym : ∀ π : Equiv.Perm (Fin (n + 1)), permB π ρ = ρ)
    (hΛ : applyFirst Λ ρ = X ⊗ₖ trA ρ)
    (hΓ : applyLast Γ (splitLast (trA ρ)) = trLast (trA ρ) ⊗ₖ Y)
    (M : Fin t → Matrix (Fin dB) (Fin dB) ℂ) (hM : IsPOVM M)
    (m : Fin (n + 1)) (w : Fin m → Fin t) (hw : 0 < pMeas ρ M m w) :
    Λ (condA ρ M m w) = X ∧ Γ (condB ρ M m w) = Y := by sorry

end DeFinettiSDP.Hierarchy
