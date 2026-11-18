-- Prove2me | Theorems.Thm_APFPaper9_PathCost_calibrated_cost_goes_below_every_floor
-- name    : APFPaper9.PathCost.calibrated_cost_goes_below_every_floor
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-17T06:46:02.005888+00:00
-- url     : https://prove2.me/theorems/c8c92cfa-2b05-4b7f-9566-9364b4d00412
-- title:
--   calibrated cost goes below every floor
-- statement:
--   Result: calibrated cost goes below every floor. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem calibrated_cost_goes_below_every_floor (d : ℝ → ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
--       (hcal : ∀ t, 0 < t → a * t ≤ d t ∧ d t ≤ b * t) (e : ℝ) (he : 0 < e) :
--       ∃ t, 0 < t ∧ 0 < d t ∧ d t < e
--   ```
--
--   Module context and limits: For a supplied real function on every positive displacement, positive linear lower and upper bounds give positive values below any floor. A token-valued function under a linear upper bound vanishes at sufficiently small displacements. This does not prove a physical calibration, arbitrary physical divisibility, or the paper's geometric substrate construction.
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper9_a_calibrated_path_cost_is_unfloored:56; pullbacks v46; source SHA-256 5a3985430927d737acaea6f297269a19d789ce56d2c76a5e415f4cefa58c6710']

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option autoImplicit false

theorem APFPaper9.PathCost.calibrated_cost_goes_below_every_floor :
∀ (d : Real → Real) (a b : Real)
  (ha : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) a)
  (hb : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) b)
  (hcal :
    ∀ (t : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t →
        And
          (@LE.le.{0} Real Real.instLE (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a t)
            (d t))
          (@LE.le.{0} Real Real.instLE (d t)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b t)))
  (e : Real)
  (he : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) e),
  @Exists.{1} Real fun (t : Real) =>
    And (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t)
      (And
        (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (d t))
        (@LT.lt.{0} Real Real.instLT (d t) e)) := by sorry
