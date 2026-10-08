-- Prove2me | Theorems.Thm_ChenStein_Process_finite_dim_bound
-- name    : ChenStein.Process.finite_dim_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:33:16.277768+00:00
-- url     : https://prove2.me/theorems/89e267c3-112d-48dc-be1b-291a2f7333cd
-- title:
--   Theorem 2 (finite-dimensional bound), p. 11 — ‖𝓛(W₁,…,W_d) − 𝓛(Z₁,…,Z_d)‖ ≤ 2(1 ∧ 1.4(min λ_i)^{−1/2})(2b₁ + 2b₂ + b₃)
-- statement:
--   Work in the setting of §2: $(X_\alpha)_{\alpha\in I}$ are Bernoulli random variables with $p_\alpha=P(X_\alpha=1)>0$, $\lambda=\sum_\alpha p_\alpha\in(0,\infty)$, and for each $\alpha$ a neighbourhood $B_\alpha\ni\alpha$ defines $b_1,b_2,b_3$. On another probability space let $(Y_\alpha)_{\alpha\in I}$ be mutually independent, $Y_\alpha$ Poisson with mean $p_\alpha$.
--
--   Partition $I$ into disjoint nonempty subsets $I(1),\dots,I(d)$ and let
--   $$W_j=\sum_{\alpha\in I(j)}X_\alpha,\qquad Z_j=\sum_{\alpha\in I(j)}Y_\alpha,\qquad \lambda_j=EW_j=EZ_j.$$
--   Then the total variation distance between the joint laws satisfies
--   $$\bigl\|\mathcal L((W_1,\dots,W_d))-\mathcal L((Z_1,\dots,Z_d))\bigr\|\le2\bigl(1\wedge1.4(\min_i\lambda_i)^{-1/2}\bigr)(2b_1+2b_2+b_3),$$
--   where, as throughout the paper, $\|\mathcal L(U)-\mathcal L(V)\|=\sup_{\|h\|=1}|Eh(U)-Eh(V)|=2\sup_A|P(U\in A)-P(V\in A)|$.
--
--   The paper presents Theorem 2 as following easily from this bound, applied to partitions whose blocks are singletons except for one block of small total mass.
--
--   **Formalization Note** The norm is written as `2 * tvDist`, with `tvDist` the supremum over measurable sets of $|\mu(A)-\nu(A)|$; the factor $2$ is the paper's normalization. $b_1,b_2,b_3$ are in $[0,\infty]$ and the comparison is made there. The partition is a surjective map $I\to\{1,\dots,d\}$ (`Fin d`, $d\ge1$), which makes the blocks disjoint, covering and nonempty. $\lambda_j$ is the real sum $\sum_{\alpha\in I(j)}p_\alpha$ (summable since $\sum p_\alpha=\lambda<\infty$), which is $EW_j=EZ_j$; $\min_i\lambda_i$ is a finite minimum. The index set is assumed countable, which loses nothing ($p_\alpha>0$ and $\sum p_\alpha<\infty$ force it) and makes the block sums measurable. Block sums are $\mathbb N$-valued `tsum`s, equal to the true sums almost surely. The $Y_\alpha$ live on their own probability space; total variation compares only laws.
-- source:
--   Arratia, Goldstein and Gordon, Two moments suffice for Poisson approximations: the Chen-Stein method, Ann. Probab. 17 (1989), p. 11, Theorem 2, finite-dimensional bound with display (2)

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_ChenStein_Process_Setting

namespace ChenStein.Process

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem finite_dim_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {I : Type*} [Countable I]
    (X : I → Ω → ℕ) (hXm : ∀ α, Measurable (X α)) (hX01 : ∀ α ω, X α ω ≤ 1)
    (hp : ∀ α, 0 < p P X α)
    (lam : ℝ) (hlam : HasSum (p P X) lam) (hlam0 : 0 < lam)
    (B : I → Set I) (hB : ∀ α, α ∈ B α)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : I → Ω' → ℕ) (hYm : ∀ α, Measurable (Y α)) (hYind : iIndepFun Y P')
    (hYlaw : ∀ α, P'.map (Y α) = poissonMeasure (p P X α).toNNReal)
    {d : ℕ} [NeZero d] (part : I → Fin d) (hpart : Function.Surjective part) :
    ENNReal.ofReal (2 * MarkovChainCLT.tvDist (P.map (Wvec X part)) (P'.map (Wvec Y part)))
      ≤ 2 * ENNReal.ofReal (min 1 (1.4 *
            (Finset.univ.inf' Finset.univ_nonempty (lamj P X part)) ^ (-(1 / 2 : ℝ))))
          * (2 * b1 P X B + 2 * b2 P X B + b3 P X B) := by sorry

end ChenStein.Process
