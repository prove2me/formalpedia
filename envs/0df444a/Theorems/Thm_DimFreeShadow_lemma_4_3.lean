-- Prove2me | Theorems.Thm_DimFreeShadow_lemma_4_3
-- name    : DimFreeShadow.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:05:43.573567+00:00
-- url     : https://prove2.me/theorems/6ab9d30e-a43f-463f-aab3-40ac823f6828
-- title:
--   Lemma 4.3 — selected rewards
-- statement:
--   Let $\{(p_x,\rho_x):x\in\mathcal X\}$ be a finite ensemble: $\mathcal X$ finite, $p_x>0$, $\sum_x p_x=1$, each $\rho_x$ a state on $\mathcal H$. Fix $N\ge1$ and let $K$ be the kernel of Eq. (17). For every stochastic map $W:\mathcal X\to[k]$ and every list of effects $0\preceq A_1,\dots,A_k\preceq I$ on $\mathcal H$,
--
--   $$
--   \Big|\sum_{x,a}p_xW(a\mid x)\operatorname{Tr}(A_a\rho_x)-\sum_{x,y,a}p_xK(y\mid x)W(a\mid y)\operatorname{Tr}(A_a\rho_x)\Big|\le\sqrt{\frac{\log k}{N}} .
--   $$
--
--   The kernel is built from the ensemble and $N$ alone, so the same $K$ works for every $W$ and every list of effects.
--
--   The logarithm is natural.
--
--   Differences from the source:
--   - encoding: a finite-dimensional Hilbert space H and its tensor powers → ℂ^d for a finite type d, with H^{⊗T} indexed by Fin T → d; reason: every finite-dimensional Hilbert space is unitarily equivalent to some ℂ^d; the same instances
--   - encoding: labels [k] = {1, …, k}, k ≥ 1 → Fin k; k ≥ 1 is not a separate hypothesis; reason: a stochastic map on the nonempty ensemble forces k ≥ 1
--   - encoding: Tr(·) of an effect times a state (a real number) → the real part .re of the complex trace; reason: the trace of a product of two Hermitian positive semidefinite matrices is real; the same value
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), Lemma 4.3, p.18

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_DimFreeShadow_outputKernel

namespace DimFreeShadow

/-- **Lemma 4.3 (selected rewards)** (arXiv:2608.06345, sha256 a1a42249…, Lemma 4.3, p.18).
For a finite ensemble `{(p_x, ρ_x)}` and a budget `N ≥ 1`, for every stochastic map
`W : X → [k]` and every list of effects `0 ⪯ A_1, …, A_k ⪯ I` on `H`, the kernel `K` of
Eq. (17) satisfies
`|Σ_{x,a} p_x W(a|x) Tr(A_a ρ_x) − Σ_{x,y,a} p_x K(y|x) W(a|y) Tr(A_a ρ_x)| ≤ √(log k / N)` (21).
The kernel `K` is built from the ensemble and `N` only, so the same kernel works for every `W`
and every list of effects.

**Formalization Note** Labels `[k]` are `Fin k`; `W x a = W(a | x)`. Natural logarithm. Traces
through real parts. `k ≥ 1` is implied by the stochasticity of `W` on the nonempty `X`. -/
theorem lemma_4_3 {X d : Type} [Fintype X] [DecidableEq X] [Fintype d] [DecidableEq d]
    (p : X → ℝ) (ρ : X → Matrix d d ℂ) (hp : ∀ x, 0 < p x) (hsum : ∑ x, p x = 1)
    (hρ : ∀ x, WildeQIT.IsDensityOperator (ρ x)) (N : ℕ) (hN : 1 ≤ N)
    (k : ℕ) (W : X → Fin k → ℝ) (hW0 : ∀ x a, 0 ≤ W x a) (hW1 : ∀ x, ∑ a, W x a = 1)
    (Aeff : Fin k → Matrix d d ℂ) (hA : ∀ a, QAlgorithms.IsEffect (Aeff a)) :
    |∑ x, ∑ a, p x * W x a * (Aeff a * ρ x).trace.re -
        ∑ x, ∑ y, ∑ a, p x * outputKernel p ρ N y x * W y a * (Aeff a * ρ x).trace.re| ≤
      Real.sqrt (Real.log k / N) := by sorry

end DimFreeShadow
