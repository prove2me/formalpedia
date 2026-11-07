-- Prove2me | Theorems.Thm_AaronsonAmbainis_Average_exists_inflR_ge_sqrt
-- name    : AaronsonAmbainis.Average.exists_inflR_ge_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:42:41.348896+00:00
-- url     : https://prove2.me/theorems/c0db60e6-a30a-4341-bd91-08723bbcb05e
-- title:
--   Average: exists infl R ge sqrt
-- statement:
--   The bound for the influences with the power `5/2` written as `Var² · √Var`: some coordinate
--   `j` has `√15 Var(f)^{5/2} ≤ 125 L(f) K² Inf_j(f)`, that is,
--   `Inf_j(f) ≥ (√15 / 125) Var(f)^{5/2} / (L(f) K²)`, where `L(f) = ∑_k L_k(f)`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Influence.lean#L191-L198
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Influence.lean#L191-L198

import Definitions.Def_AaronsonAmbainis_Average_Iterate
import Definitions.Def_AaronsonAmbainis_Average_Influence
set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Average
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Average.exists_inflR_ge_sqrt (hI : InfluenceBound) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    {K : ℝ} (ha : ∀ x i, 0 ≤ a x i) (hsum : ∀ x, ∑ i, a x i ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i) (hvar : 0 < variance f) :
    ∃ j, Real.sqrt 15 * (variance f ^ 2 * Real.sqrt (variance f))
      ≤ 125 * (∑ k, meanAbsIncr f k) * K ^ 2 * inflR f j := by sorry
