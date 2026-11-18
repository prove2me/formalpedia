-- Prove2me | Theorems.Thm_APFPaper5_K3_Connections_single_reads_agree_iff
-- name    : APFPaper5.K3.Connections.single_reads_agree_iff
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-17T06:25:50.667761+00:00
-- url     : https://prove2.me/theorems/7282d268-850f-4b00-86c1-e5d8920d2aa6
-- title:
--   single reads agree iff
-- statement:
--   Result: single reads agree iff. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem single_reads_agree_iff (W W' : ι → ι → ℝ) :
--       (∀ i, read W (alt i) = read W' (alt i)) ↔ ∀ i, W i i = W' i i
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
--   ['Theorems.Thm_APFPaper5_K3_free_number_on_each_connection:152; pullbacks v46; source SHA-256 9a7e70cb6a988b5fe9640fbbbd2eb2106425cc5f870aa5a31e48706f7f67de9d']

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

theorem APFPaper5.K3.Connections.single_reads_agree_iff :
∀ {ι : Type apfNative_u_1} [inst : Fintype.{apfNative_u_1} ι] [inst_1 : DecidableEq.{apfNative_u_1 + 1} ι]
  (W W' : ι → ι → Real),
  Iff
    (∀ (i : ι),
      @Eq.{1} Real
        (@APFPaper5.K3.Connections.read.{apfNative_u_1} ι inst W
          (@APFPaper5.K3.Connections.alt.{apfNative_u_1} ι inst_1 i))
        (@APFPaper5.K3.Connections.read.{apfNative_u_1} ι inst W'
          (@APFPaper5.K3.Connections.alt.{apfNative_u_1} ι inst_1 i)))
    (∀ (i : ι), @Eq.{1} Real (W i i) (W' i i)) := by sorry
