-- Prove2me | Theorems.Thm_APFPaper5_K3_Carrying_relative_turn_is_counted
-- name    : APFPaper5.K3.Carrying.relative_turn_is_counted
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-17T04:30:22.490282+00:00
-- url     : https://prove2.me/theorems/be9ea560-258d-4aac-bfb9-a17edb946aaa
-- title:
--   relative turn is counted
-- statement:
--   Result: relative turn is counted. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem relative_turn_is_counted (c s : ℝ) (hcs : c * c + s * s = 1) (u : ℝ × ℝ)
--       (hu : u.1 * u.1 + u.2 * u.2 = 1) : meet (turnBy c s u) u = 2 + 2 * c
--   ```
--
--   Module context and limits: A supplied difference-of-state-function charge telescopes and vanishes on loops. Every loop step vanishes only with the explicit nondecreasing-state-function hypothesis. Endpoint changes of presentation preserve closed totals and relative path charges; distinct-endpoint open totals can be gauged to zero. Squared-sum interference is a supplied rule, not a derived physical gauge law.
--
--   Source scope parameters:
--
--   ```lean
--   universe u
--   variable {X : Type u}
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K3_what_a_charge_on_carrying_does:181; pullbacks v46; source SHA-256 33f3ddc9be53cf5c8fd3b4910cdc800399115b1303cae64af5c903867e689ce9']

import Definitions.Def_APFPaper5_K3_what_a_charge_on_carrying_does_Vocabulary
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit false

theorem APFPaper5.K3.Carrying.relative_turn_is_counted :
∀ (c s : Real)
  (hcs :
    @Eq.{1} Real
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c c)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) s s))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (u : Prod.{0, 0} Real Real)
  (hu :
    @Eq.{1} Real
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Prod.fst.{0, 0} Real Real u)
          (@Prod.fst.{0, 0} Real Real u))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Prod.snd.{0, 0} Real Real u)
          (@Prod.snd.{0, 0} Real Real u)))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
  @Eq.{1} Real (APFPaper5.K3.Carrying.meet (APFPaper5.K3.Carrying.turnBy c s u) u)
    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
      (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
        c)) := by sorry
