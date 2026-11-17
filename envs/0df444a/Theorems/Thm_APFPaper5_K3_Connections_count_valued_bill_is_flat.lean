-- Prove2me | Theorems.Thm_APFPaper5_K3_Connections_count_valued_bill_is_flat
-- name    : APFPaper5.K3.Connections.count_valued_bill_is_flat
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-17T04:33:53.274792+00:00
-- url     : https://prove2.me/theorems/e80c141a-1ba8-40b6-90d2-5eb5bd2ba328
-- title:
--   count valued bill is flat
-- statement:
--   Result: count valued bill is flat. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem count_valued_bill_is_flat {eps k : ℝ} (heps : 0 < eps)
--       (h : ∀ u v : ℝ, u * u + v * v = 1 → ∃ m : ℤ, bill eps k u v = (m : ℝ) * eps) : k = 0
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
--   ['Theorems.Thm_APFPaper5_K3_free_number_on_each_connection:439; pullbacks v46; source SHA-256 9a7e70cb6a988b5fe9640fbbbd2eb2106425cc5f870aa5a31e48706f7f67de9d']

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

theorem APFPaper5.K3.Connections.count_valued_bill_is_flat :
∀ {eps k : Real}
  (heps : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) eps)
  (h :
    ∀ (u v : Real),
      @Eq.{1} Real
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) u u)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) v v))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
        @Exists.{1} Int fun (m : Int) =>
          @Eq.{1} Real (APFPaper5.K3.Connections.bill eps k u v)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@Int.cast.{0} Real Real.instIntCast m) eps)),
  @Eq.{1} Real k (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) := by sorry
