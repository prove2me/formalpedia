-- Prove2me | Theorems.Thm_DynStochMatching_Reward_claim_6
-- name    : DynStochMatching.Reward.claim_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T20:43:39.10715+00:00
-- url     : https://prove2.me/theorems/a97e7877-f13c-4c90-a6b2-e369c96e1fa9
-- title:
--   Claim 6 — Boundary coordinates in monotone sets
-- statement:
--   Let x≤y be count vectors and A an upward-closed set containing x. For each coordinate in the image of the boundary map φ, equivalently each positive coordinate of y whose downward transition has positive printed actual-generator rate and exits A, the corresponding counts in x and y are equal. Natural counts make the printed absolute-value signs redundant.
--
--   Source statement:
--
--   $|x_{i,\ell}|=|y_{i,\ell}|$ for every $(i,\ell)\in\varphi\langle Z_{\bar A}\rangle$.
--
--   Differences from the source:
--   - generalization: a finite collection of arriving types → Fin n also permits the empty type graph; reason: the empty instance has zero rewards, flows and costs; restricting to nonempty graphs recovers every source instance
--   - generalization: boundary coordinates of the constructed feasible policy flow → boundary coordinates for any flow parameter; reason: the coordinate identity follows from the upward-set geometry and the stated downward transition condition alone
--   - encoding: absolute values of population coordinates and image of φ → natural counts and the set of positive downward-exit coordinates; reason: counts are nonnegative and the downward coordinate uniquely specifies φ
-- source:
--   Aouad and Sarıtaç (2022), Dynamic Stochastic Matching Under Limited Time, https://doi.org/10.1287/opre.2022.2293, held published-basis manuscript, Claim 6, printed p. 51 / PDF p. 52

import Definitions.Def_DynStochMatching_Reward_CountChains

open MeasureTheory Filter
open scoped ENNReal Classical

namespace DynStochMatching.Reward

theorem claim_6 {n : ℕ} (D : Instance n) (flow : Flow n)
    (x y : CountState n) (A : Set (CountState n))
    (hxy : x ≤ y) (hupper : IsUpperSet A) (hx : x ∈ A) :
    ∀ a ∈ boundaryCoordinates D flow y A, x a = y a := by sorry

end DynStochMatching.Reward
