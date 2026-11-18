-- Prove2me | Theorems.Thm_APFPaper9_PathCost_token_cost_under_a_path_bound_vanishes_nearby
-- name    : APFPaper9.PathCost.token_cost_under_a_path_bound_vanishes_nearby
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-17T06:52:38.612199+00:00
-- url     : https://prove2.me/theorems/46a58212-97ee-41b8-8b68-08287affa414
-- title:
--   token cost under a path bound vanishes nearby
-- statement:
--   Result: token cost under a path bound vanishes nearby. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem token_cost_under_a_path_bound_vanishes_nearby (d : ℝ → ℝ) (e b : ℝ)
--       (htoken : ∀ t, 0 < t → d t = 0 ∨ e ≤ d t) (hb : ∀ t, 0 < t → d t ≤ b * t)
--       (t : ℝ) (ht : 0 < t) (hsmall : b * t < e) : d t = 0
--   ```
--
--   Module context and limits: For a supplied real function on every positive displacement, positive linear lower and upper bounds give positive values below any floor. A token-valued function under a linear upper bound vanishes at sufficiently small displacements. This does not prove a physical calibration, arbitrary physical divisibility, or the paper's geometric substrate construction.
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper9_a_calibrated_path_cost_is_unfloored:84; pullbacks v46; source SHA-256 5a3985430927d737acaea6f297269a19d789ce56d2c76a5e415f4cefa58c6710']

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option autoImplicit false

theorem APFPaper9.PathCost.token_cost_under_a_path_bound_vanishes_nearby :
∀ (d : Real → Real) (e b : Real)
  (htoken :
    ∀ (t : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t →
        Or (@Eq.{1} Real (d t) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
          (@LE.le.{0} Real Real.instLE e (d t)))
  (hb :
    ∀ (t : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t →
        @LE.le.{0} Real Real.instLE (d t) (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b t))
  (t : Real)
  (ht : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t)
  (hsmall : @LT.lt.{0} Real Real.instLT (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b t) e),
  @Eq.{1} Real (d t) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) := by sorry
