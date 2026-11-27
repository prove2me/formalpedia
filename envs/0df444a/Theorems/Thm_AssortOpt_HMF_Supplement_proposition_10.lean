-- Prove2me | Theorems.Thm_AssortOpt_HMF_Supplement_proposition_10
-- name    : AssortOpt.HMF.Supplement.proposition_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T07:22:30.655808+00:00
-- url     : https://prove2.me/theorems/7c1c3acc-7604-4387-98e0-b9484097aac8
-- title:
--   Proposition 10 — the full submodularity correspondence for IC mechanisms
-- statement:
--   For any finite list distribution and any monotone submodular function $f:2^N\to[0,1]$, define
--   $$x_{\ell_k}(\ell)=f(\ell_{1:k})-f(\ell_{1:k-1}).$$
--   This mechanism is IC. No normalization $f(\varnothing)=0$ is required.
--
--   Conversely, suppose the IC constraints apply to every possible list of distinct items, including all probability-zero reports. For any such IC mechanism $x$, the function
--   $$f(S)=\max_{\ell}\sum_{j\in S\cap\ell}x_j(\ell)$$
--   is monotone, submodular and $[0,1]$-valued. Submodularity means $f(A\cup B)+f(A\cap B)\le f(A)+f(B)$ for every $A,B\subseteq N$.
--
--   This result relates ordinal incentive compatibility to a reusable class of set functions. The all-list assumption belongs only to the converse, and is not imposed on the list distribution in either randomized-assortment theorem.
--
--   Differences from the source:
--   - encoding: items N={1,…,n} and a finite list distribution → 0-based Fin n and the published ListDist with strictly positive support of Nodup lists; reason: the same finite distributions, including empty lists and n=0, are represented
--   - encoding: all possible reports including probability-zero lists in the converse only → IsICOn (allReports n) x in the converse and published IsIC D in the forward clause; reason: the report domain must be separate from strictly positive probability support
--   - encoding: f(S) = max over ℓ ∈ ℒ of Σ_{j∈S∩ℓ} x_j(ℓ), ℒ all possible lists → maxMass (allReports n) x S, the attained finite maximum with zero adjoined; reason: under IC every sum is nonnegative and the empty list is a report, so adjoining zero does not change the maximum
-- source:
--   Ma, When is Assortment Optimization Optimal?, arXiv:2105.10433v5, p. 23, Proposition 10

import Mathlib
import Definitions.Def_AssortOpt_HMF_Supplement_Reports

namespace AssortOpt.HMF.Supplement

theorem proposition_10 {n : ℕ} :
    (∀ (D : ListDist n) (f : Finset (Fin n) → ℝ), IsIncreasingSetFn f →
        NonmonotoneSubmod.Shared.Submodular f → IsIC D (incrementMech f)) ∧
    (∀ x : List (Fin n) → Fin n → ℝ, IsICOn (allReports n) x →
      IsIncreasingSetFn (maxMass (allReports n) x) ∧
        NonmonotoneSubmod.Shared.Submodular (maxMass (allReports n) x)) := by sorry

end AssortOpt.HMF.Supplement
