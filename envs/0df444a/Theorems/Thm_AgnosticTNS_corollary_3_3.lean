-- Prove2me | Theorems.Thm_AgnosticTNS_corollary_3_3
-- name    : AgnosticTNS.corollary_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:34:30.520945+00:00
-- url     : https://prove2.me/theorems/7796da49-7478-4bb3-8f93-7e4fd5f4c48a
-- title:
--   Corollary 3.3 — one-step agnostic disentangling
-- statement:
--   Let $\rho\ge0$ be a subnormalised state on $\mathcal H_A\otimes\mathcal H_B$ with $\mathrm{tr}(\rho)\le1$, and $|\phi\rangle$ a vector of norm at most one and Schmidt rank at most $r$ across $A\mid B$. Let $\sigma_A=\mathrm{tr}_B(\rho)$ and let $\hat\sigma_A\ge0$ satisfy $\|\sigma_A-\hat\sigma_A\|_1\le\gamma$. Let $\Lambda\in\{1,\dots,\dim\mathcal H_A\}$, let $W$ be the span of $\Lambda$ orthonormal eigenvectors of $\hat\sigma_A$ for its $\Lambda$ largest eigenvalues, counted with multiplicity, and let $\Pi$ be any orthogonal projector on $\mathcal H_A$ whose range contains $W$. Then
--   $$
--   \big|\langle\phi|(\Pi\otimes I_B)\rho(\Pi\otimes I_B)|\phi\rangle-\langle\phi|\rho|\phi\rangle\big|\le2\sqrt{r\Big(\frac1{\Lambda+1}+2\gamma\Big)} .
--   $$
--   This bounds the overlap lost in one compression step of the agnostic learner.
--
--   Differences from the source:
--   - encoding: $\mathcal H_A\otimes\mathcal H_B$, $\Pi\otimes I_B$, Schmidt rank, orthogonal projectors, $\|\cdot\|_\infty$, $\mathrm{tr}_B$ → bases `α × β`, `Matrix.kronecker P 1`, rank of the coefficient matrix $(a,b)\mapsto\phi(a,b)$, matrices with $P^2=P=P^\dagger$, `opNorm`, `WildeQIT.partialTraceRight`; reason: Lean convention; same instances
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Corollary 3.3, Eqs. (3.19)–(3.21), p.18

import Mathlib
import Definitions.Def_AgnosticTNS_expVal
import Definitions.Def_AgnosticTNS_IsTopSpan
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_WildeQIT_traceNorm
open Matrix
open scoped ComplexOrder

namespace AgnosticTNS

/-- **Corollary 3.3 (One-step agnostic disentangling)**, p.18 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)). Let `ρ ≥ 0` on `H_A ⊗ H_B` with
`tr ρ ≤ 1`, `|ϕ⟩` of norm at most one and Schmidt rank at most `r` across `A | B`, `σ_A = tr_B(ρ)`
(3.19), `σ̂_A ≥ 0` with `‖σ_A − σ̂_A‖₁ ≤ γ` (3.20), `Λ ∈ {1, …, dim H_A}`, `W` the span of `Λ`
orthonormal eigenvectors of `σ̂_A` for its `Λ` largest eigenvalues counted with multiplicity, and `Π`
any orthogonal projector on `H_A` whose range contains `W`. Then
`|⟨ϕ|(Π ⊗ I_B)ρ(Π ⊗ I_B)|ϕ⟩ − ⟨ϕ|ρ|ϕ⟩| ≤ 2 √(r (1/(Λ + 1) + 2γ))` (3.21).

**Formalization Note** As in Lemma 3.1; `‖·‖₁` is the published `WildeQIT.traceNorm`. -/
theorem corollary_3_3 {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ρ : Matrix (α × β) (α × β) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace.re ≤ 1)
    (φ : α × β → ℂ) (hφ : ∑ x, ‖φ x‖ ^ 2 ≤ 1) (r : ℕ)
    (hr : (Matrix.of fun a b => φ (a, b)).rank ≤ r)
    (σh : Matrix α α ℂ) (hσh : σh.PosSemidef) (γ : ℝ)
    (hγ : WildeQIT.traceNorm (WildeQIT.partialTraceRight ρ - σh) ≤ γ)
    (Λ : ℕ) (hΛ1 : 1 ≤ Λ) (hΛD : Λ ≤ Fintype.card α) (W : Submodule ℂ (α → ℂ))
    (hW : IsTopSpan σh Λ W) (P : Matrix α α ℂ) (hP : P * P = P) (hPh : Pᴴ = P)
    (hWP : W ≤ LinearMap.range P.mulVecLin) :
    |expVal (Matrix.kronecker P (1 : Matrix β β ℂ) * ρ * Matrix.kronecker P 1) φ - expVal ρ φ| ≤
      2 * Real.sqrt (r * (1 / (Λ + 1) + 2 * γ)) := by sorry

end AgnosticTNS
