-- Prove2me | Theorems.Thm_ConsistentSubmodular_Shadow_LeftLaw_core
-- name    : ConsistentSubmodular.Shadow.LeftLaw.core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:30.438684+00:00
-- url     : https://prove2.me/theorems/466dad0e-fd8e-4403-8218-41b4ae6f6eeb
-- title:
--   Inequality (7) after normalization — the unit-mass bound
-- statement:
--   Let $\alpha\in[0,1]$ be such that every instance of nonincreasing consecutive intervals with the equalizing distribution has adaptivity gap at least $\alpha$ (the chain hypothesis of Lemma 3). Let $L$ be a finite law of left endpoints: weights $p_j\ge 0$ with $\sum_j p_j=1$ on points $\ell_j$, with a number $\mathrm{low}\le \ell_j$ whenever $p_j\neq 0$, attained or undercut by some atom of positive weight ($\ell_j\le \mathrm{low}$ for some $j$ with $p_j\ne0$). Write
--   $$B=\sum_j p_j\ell_j,\qquad H(x)=\sum_j p_j\,(x-\ell_j)^+ .$$
--   Assume $\mathrm{low}\ge 0$, and let $r_j$ be reals such that for every $j$ with $p_j\neq 0$:
--
--   1. $\ell_j\le r_j$;
--   2. $H(r_j)-H(\ell_j)\le 1$.
--
--   Then
--   $$\alpha\Big(B+\sum_j p_j\,(r_j-\ell_j)\Big)\;\le\; B+1 .$$
--
--   This is inequality (7) in its normalized form, where the intervals $[\ell_j,r_j]$ have total overlap mass at most $1$ with the random left endpoint. It is the core estimate of the shadow reduction in the proof of Lemma 3, and it is applied after rescaling by $M$ to obtain the general case.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/StepIntegrals.lean#L440-L506 (`ConsistentSubmodular.Shadow.LeftLaw.core`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_StepIntegrals

open scoped BigOperators Topology
open MeasureTheory Filter Set
open ConsistentSubmodular ConsistentSubmodular.Shadow
open ConsistentSubmodular.Shadow.LeftLaw
variable {ι : Type*} [Fintype ι] (L : LeftLaw ι)

theorem ConsistentSubmodular.Shadow.LeftLaw.core {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hchain : ChainHypothesis α)
    (hlow : 0 ≤ L.low) (r : ι → ℝ) (hr : ∀ j, L.prob j ≠ 0 → L.left j ≤ r j)
    (hM : ∀ j, L.prob j ≠ 0 → L.ramp (r j) - L.ramp (L.left j) ≤ 1) :
    α * (L.mean + ∑ j, L.prob j * (r j - L.left j)) ≤ L.mean + 1 := by sorry
