-- Prove2me | Theorems.Thm_APFPaper5_K3_Connections_pair_neg_left
-- name    : APFPaper5.K3.Connections.pair_neg_left
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-17T06:12:23.751829+00:00
-- url     : https://prove2.me/theorems/0bad93ac-1de9-49d6-972c-41b8ade3db73
-- title:
--   pair neg left
-- statement:
--   Result: pair neg left. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   omit [DecidableEq ι] in
--   theorem pair_neg_left (W : ι → ι → ℝ) (x z : ι → ℝ) :
--       pair W (fun a => -x a) z = -pair W x z
--   ```
--
--   Module context and limits: For a supplied finite real table, single basis reads fix its diagonal and symmetric pair reads determine the remaining entries. A quadratic bill on the unit circle is flat exactly when its cross price is zero; positive cross price fixes the minimizing table, not a unique signed vector. These are algebraic table and circle results, not constructed physical states, chances, or prices.
--
--   Source scope parameters:
--
--   ```lean
--   variable {ι : Type*} [Fintype ι] [DecidableEq ι]
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K3_free_number_on_each_connection:128; pullbacks v46; source SHA-256 9a7e70cb6a988b5fe9640fbbbd2eb2106425cc5f870aa5a31e48706f7f67de9d']

import Definitions.Def_APFPaper5_K3_free_number_on_each_connection_Vocabulary
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Algebra.Order.Ring.Cast
set_option autoImplicit false
universe apfNative_u_1

theorem APFPaper5.K3.Connections.pair_neg_left :
∀ {ι : Type apfNative_u_1} [inst : Fintype.{apfNative_u_1} ι] (W : ι → ι → Real) (x z : ι → Real),
  @Eq.{1} Real
    (@APFPaper5.K3.Connections.pair.{apfNative_u_1} ι inst W (fun (a : ι) => @Neg.neg.{0} Real Real.instNeg (x a)) z)
    (@Neg.neg.{0} Real Real.instNeg (@APFPaper5.K3.Connections.pair.{apfNative_u_1} ι inst W x z)) := by sorry
