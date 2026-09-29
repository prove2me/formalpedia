-- Prove2me | Theorems.Thm_CKLaneA3X_Encl_mul
-- name    : CKLaneA3X.Encl.mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T01:47:31.272977+00:00
-- url     : https://prove2.me/theorems/546f59d6-9aac-4c5a-bc72-1efd5a77ff83
-- title:
--   Multiplication preserves A3X polynomial enclosures
-- statement:
--   Multiplying two function enclosures gives the exact truncated-product enclosure, with the original coefficient-bound, vanishing-prefix, order, and remainder hypotheses. This is the source multiplication soundness theorem, independent of any particular numerical cell.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneA3X/TM.lean#L193

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Definitions.Def_A3X_numeric_core
import Definitions.Def_A3X_enclosure

open CKLaneA3X

theorem CKLaneA3X.Encl.mul {f g : ℝ → ℝ → ℝ} {P Q R : TPoly} {β γ : List ℚ} {r1 r2 r : ℚ}
    {n1 n2 v1 v2 n : ℕ}
    (hf : Encl f P r1 n1) (bP : EntryBnd P β) (hg : Encl g Q r2 n2) (bQ : EntryBnd Q γ)
    (hz1 : zeroPrefix P v1 = true) (hz2 : zeroPrefix Q v2 = true)
    (hv1 : v1 ≤ n1) (hn1 : n ≤ v1 + n2) (hn2 : n ≤ v2 + n1)
    (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2)
    (hR : TPoly.mulT P Q n = R)
    (hrem : HB β γ n + (bsum (ldrop β v1) + r1 * Tq ^ (n1 - v1)) * r2 * Tq ^ (v1 + n2 - n)
        + bsum (ldrop γ v2) * r1 * Tq ^ (v2 + n1 - n) ≤ r) :
    Encl (fun t ρ => f t ρ * g t ρ) R r n := by sorry
