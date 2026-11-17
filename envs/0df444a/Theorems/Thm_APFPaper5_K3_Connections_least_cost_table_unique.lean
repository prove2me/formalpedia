-- Prove2me | Theorems.Thm_APFPaper5_K3_Connections_least_cost_table_unique
-- name    : APFPaper5.K3.Connections.least_cost_table_unique
-- status  : Open
-- author  : @FiniteUniverse
-- created : 2026-11-17T05:56:25.806709+00:00
-- url     : https://prove2.me/theorems/09df6dfc-9a32-4a6a-8680-f07f7d053557
-- title:
--   least cost table unique
-- statement:
--   Result: least cost table unique. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem least_cost_table_unique {eps k : ℝ} (hk : 0 < k) {u v u' v' : ℝ}
--       (h : u * u + v * v = 1) (h' : u' * u' + v' * v' = 1)
--       (hmin : bill eps k u v = eps - k) (hmin' : bill eps k u' v' = eps - k) :
--       u * u = u' * u' ∧ v * v = v' * v' ∧ u * v = u' * v'
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
--   ['Theorems.Thm_APFPaper5_K3_free_number_on_each_connection:360; pullbacks v46; source SHA-256 9a7e70cb6a988b5fe9640fbbbd2eb2106425cc5f870aa5a31e48706f7f67de9d']

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

theorem APFPaper5.K3.Connections.least_cost_table_unique :
∀ {eps k : Real}
  (hk : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) k)
  {u v u' v' : Real}
  (h :
    @Eq.{1} Real
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) u u)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) v v))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (h' :
    @Eq.{1} Real
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) u' u')
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) v' v'))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hmin :
    @Eq.{1} Real (APFPaper5.K3.Connections.bill eps k u v)
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) eps k))
  (hmin' :
    @Eq.{1} Real (APFPaper5.K3.Connections.bill eps k u' v')
      (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub) eps k)),
  And
    (@Eq.{1} Real (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) u u)
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) u' u'))
    (And
      (@Eq.{1} Real (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) v v)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) v' v'))
      (@Eq.{1} Real (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) u v)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) u' v'))) := by sorry
