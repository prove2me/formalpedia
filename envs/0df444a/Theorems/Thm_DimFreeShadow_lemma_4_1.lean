-- Prove2me | Theorems.Thm_DimFreeShadow_lemma_4_1
-- name    : DimFreeShadow.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:04:55.376065+00:00
-- url     : https://prove2.me/theorems/baf499ca-1864-4144-ac6b-b1a2f0798d00
-- title:
--   Lemma 4.1 — the recovery PGM is a POVM with a $p$-reversible kernel
-- statement:
--   Let $\{(p_x,\rho_x):x\in\mathcal X\}$ be a finite ensemble: $\mathcal X$ finite, $p_x>0$, $\sum_x p_x=1$, each $\rho_x$ a state on $\mathcal H$. Fix $N\ge1$. For every $0\le t<N$ the effects $\{D_{y,t}\}_y$ of Eq. (5) form a POVM on $\mathcal H^{\otimes t}$, and $\operatorname{supp}(\rho_x^{\otimes t})\subseteq\operatorname{supp}(B_t)$ for every $x$. Moreover
--
--   $$
--   \sum_y K_t(y\mid x)=1,\qquad\sum_x p_xK_t(y\mid x)=p_y,\qquad p_xK_t(y\mid x)=p_yK_t(x\mid y),
--   $$
--
--   and the same three identities hold with $K$ in place of $K_t$.
--
--   Reversibility of the kernel is what lets Corollary 4.4 exchange the roles of $x$ and $y$ in the second reward.
--
--   Differences from the source:
--   - encoding: a finite-dimensional Hilbert space H and its tensor powers → ℂ^d for a finite type d, with H^{⊗T} indexed by Fin T → d; reason: every finite-dimensional Hilbert space is unitarily equivalent to some ℂ^d; the same instances
--   - encoding: supp(ρ_x^{⊗t}) ⊆ supp(B_t) → ker B_t ≤ ker ρ_x^{⊗t}; reason: equivalent for Hermitian matrices, since the support is the orthogonal complement of the kernel
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), Lemma 4.1, p.16

import Mathlib
import Definitions.Def_ShadowTomography_UpperBound_tensorPow
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_DimFreeShadow_recoveryEffect
import Definitions.Def_DimFreeShadow_outputKernel

namespace DimFreeShadow

open ShadowTomography.UpperBound (tensorPow)

/-- **Lemma 4.1** (arXiv:2608.06345, sha256 a1a42249…, Lemma 4.1, p.16). For a finite ensemble
`{(p_x, ρ_x)}` with positive weights summing to one and a budget `N ≥ 1`: for every
`0 ≤ t < N` the effects `{D_{y,t}}_y` of Eq. (5) form a POVM on `H^{⊗t}`; for every `x`,
`supp(ρ_x^{⊗t}) ⊆ supp(B_t)`; the kernel `K_t` of Eq. (17) satisfies
`Σ_y K_t(y|x) = 1`, `Σ_x p_x K_t(y|x) = p_y`, `p_x K_t(y|x) = p_y K_t(x|y)` (18); and the same
three identities hold for `K`.

**Formalization Note** Support inclusion `supp A ⊆ supp B` is `ker B ⊆ ker A` (equivalent for
Hermitian matrices). The POVM condition is the published `QAlgorithms.IsPOVM`. -/
theorem lemma_4_1 {X d : Type} [Fintype X] [DecidableEq X] [Fintype d] [DecidableEq d]
    (p : X → ℝ) (ρ : X → Matrix d d ℂ) (hp : ∀ x, 0 < p x) (hsum : ∑ x, p x = 1)
    (hρ : ∀ x, WildeQIT.IsDensityOperator (ρ x)) (N : ℕ) (hN : 1 ≤ N) :
    (∀ t, t < N → QAlgorithms.IsPOVM (recoveryEffect p ρ t)) ∧
    (∀ t, t < N → ∀ x, LinearMap.ker (ensembleState p ρ t).mulVecLin ≤
      LinearMap.ker (tensorPow (ρ x) t).mulVecLin) ∧
    (∀ t, t < N → ∀ x, ∑ y, outputKernelT p ρ t y x = 1) ∧
    (∀ t, t < N → ∀ y, ∑ x, p x * outputKernelT p ρ t y x = p y) ∧
    (∀ t, t < N → ∀ x y, p x * outputKernelT p ρ t y x = p y * outputKernelT p ρ t x y) ∧
    (∀ x, ∑ y, outputKernel p ρ N y x = 1) ∧
    (∀ y, ∑ x, p x * outputKernel p ρ N y x = p y) ∧
    (∀ x y, p x * outputKernel p ρ N y x = p y * outputKernel p ρ N x y) := by sorry

end DimFreeShadow
