-- Prove2me | Theorems.Thm_ConsistentSubmodular_Shadow_LeftLaw_core_le
-- name    : ConsistentSubmodular.Shadow.LeftLaw.core_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:23.446114+00:00
-- url     : https://prove2.me/theorems/bbf31a4f-5830-4303-9176-570ec926dc66
-- title:
--   Inequality (7) — the bound $\alpha(B+C)\le B+M$
-- statement:
--   Let $\alpha\in[0,1]$ satisfy the chain hypothesis (every instance of nonincreasing consecutive intervals with the equalizing distribution has adaptivity gap at least $\alpha$). Let $L$ be a finite law of left endpoints with weights $p_j$ and points $\ell_j$, with mean $B=\sum_j p_j\ell_j$ and smallest support point $\mathrm{low}\ge 0$. Let $r_j$ be reals with $\ell_j\le r_j$ for every $j$ with $p_j\ne 0$, and let $M\in\mathbb R$ satisfy, for every $i$ with $p_i\neq 0$,
--   $$\sum_j p_j\,\max\bigl(0,\; r_i-\max(\ell_i,\ell_j)\bigr)\;\le\; M .$$
--   (The summand is the length of $[\ell_i,r_i]\cap[\ell_j,\infty)$.) Then, with $C=\sum_j p_j(r_j-\ell_j)$,
--   $$\alpha\,(B+C)\;\le\; B+M .$$
--
--   This is inequality (7) of the shadow reduction in the proof of Lemma 3. For $M>0$ it follows from the normalized version by dividing all endpoints by $M$; for $M\le 0$ every interval of positive probability degenerates to a point.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/StepIntegrals.lean#L520-L578 (`ConsistentSubmodular.Shadow.LeftLaw.core_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_StepIntegrals

open scoped BigOperators Topology
open MeasureTheory Filter Set
open ConsistentSubmodular ConsistentSubmodular.Shadow
open ConsistentSubmodular.Shadow.LeftLaw
variable {ι : Type*} [Fintype ι] (L : LeftLaw ι)

theorem ConsistentSubmodular.Shadow.LeftLaw.core_le {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hchain : ChainHypothesis α)
    (hlow : 0 ≤ L.low) (r : ι → ℝ) (hr : ∀ j, L.prob j ≠ 0 → L.left j ≤ r j) {M : ℝ}
    (hM : ∀ i, L.prob i ≠ 0 → ∑ j, L.prob j * max 0 (r i - max (L.left i) (L.left j)) ≤ M) :
    α * (L.mean + ∑ j, L.prob j * (r j - L.left j)) ≤ L.mean + M := by sorry
