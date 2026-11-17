-- Prove2me | Theorems.Thm_APFPaper5_K3_Connections_flip_connection
-- name    : APFPaper5.K3.Connections.flip_connection
-- status  : Open
-- author  : @FiniteUniverse
-- created : 2026-11-17T05:54:29.579501+00:00
-- url     : https://prove2.me/theorems/1d4f2e8d-4252-49ee-944f-9091a2489b62
-- title:
--   flip connection
-- statement:
--   Result: flip connection. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   omit [Fintype ι] [DecidableEq ι] in
--
--   theorem flip_connection (s : ι → ℝ) (W : ι → ι → ℝ) {i j : ι} (hi : s i = 1) (hj : s j = -1) :
--       flip s W i j = -W i j
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
--   ['Theorems.Thm_APFPaper5_K3_free_number_on_each_connection:265; pullbacks v46; source SHA-256 9a7e70cb6a988b5fe9640fbbbd2eb2106425cc5f870aa5a31e48706f7f67de9d']

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

theorem APFPaper5.K3.Connections.flip_connection :
∀ {ι : Type apfNative_u_1} (s : ι → Real) (W : ι → ι → Real) {i j : ι}
  (hi : @Eq.{1} Real (s i) (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hj :
    @Eq.{1} Real (s j)
      (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))),
  @Eq.{1} Real (@APFPaper5.K3.Connections.flip.{apfNative_u_1} ι s W i j) (@Neg.neg.{0} Real Real.instNeg (W i j)) := by sorry
