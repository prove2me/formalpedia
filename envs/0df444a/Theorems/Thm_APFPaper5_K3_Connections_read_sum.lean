-- Prove2me | Theorems.Thm_APFPaper5_K3_Connections_read_sum
-- name    : APFPaper5.K3.Connections.read_sum
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-17T06:13:49.018307+00:00
-- url     : https://prove2.me/theorems/059a3d8e-f5a3-422f-bef5-161a00f70a0e
-- title:
--   read sum
-- statement:
--   Result: read sum. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem read_sum (W : ι → ι → ℝ) (hW : IsSymm W) (i j : ι) :
--       read W (fun a => alt i a + alt j a) = W i i + W j j + 2 * W i j
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
--   ['Theorems.Thm_APFPaper5_K3_free_number_on_each_connection:207; pullbacks v46; source SHA-256 9a7e70cb6a988b5fe9640fbbbd2eb2106425cc5f870aa5a31e48706f7f67de9d']

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

theorem APFPaper5.K3.Connections.read_sum :
∀ {ι : Type apfNative_u_1} [inst : Fintype.{apfNative_u_1} ι] [inst_1 : DecidableEq.{apfNative_u_1 + 1} ι]
  (W : ι → ι → Real) (hW : @APFPaper5.K3.Connections.IsSymm.{apfNative_u_1} ι W) (i j : ι),
  @Eq.{1} Real
    (@APFPaper5.K3.Connections.read.{apfNative_u_1} ι inst W fun (a : ι) =>
      @HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@APFPaper5.K3.Connections.alt.{apfNative_u_1} ι inst_1 i a)
        (@APFPaper5.K3.Connections.alt.{apfNative_u_1} ι inst_1 j a))
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (W i i) (W j j))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        (W i j))) := by sorry
