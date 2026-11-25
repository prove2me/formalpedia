-- Prove2me | Theorems.Thm_Bl_general_b_fact_third_version_goal1
-- name    : Bl.general_b_fact_third_version.goal1
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:41:32.554351+00:00
-- url     : https://prove2.me/theorems/4ba738b1-2fbe-5d2a-857b-8d92fa00d74b
-- title:
--   general b fact third version: goal1
-- statement:
--   The general b fact third version construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactThirdVersion/Imports.lean#L5-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactThirdVersion/Imports.lean#L5-L152

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactThirdVersion_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_third_version

theorem Bl.general_b_fact_third_version.goal1 :
  ∀ {E : Type} [inst : Field.{0} E] [@NumberField.{0} E inst] {V : Type} [inst_2 : AddCommGroup.{0} V]
  [inst_3 :
    @Module.{0, 0} E V
      (@DivisionSemiring.toSemiring.{0} E (@Semifield.toDivisionSemiring.{0} E (@Field.toSemifield.{0} E inst)))
      (@AddCommGroup.toAddCommMonoid.{0} V inst_2)]
  [inst_4 :
    @Module.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
      (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
        (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
          (@NumberField.instCommRingRingOfIntegers.{0} E inst)))
      (@AddCommGroup.toAddCommMonoid.{0} V inst_2)]
  [inst_5 :
    @IsScalarTower.{0, 0, 0} (@NumberField.RingOfIntegers.{0} E inst) E V
      (@Algebra.toSMul.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) E
        (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
          (@NumberField.instCommRingRingOfIntegers.{0} E inst))
        (@DivisionSemiring.toSemiring.{0} E (@Semifield.toDivisionSemiring.{0} E (@Field.toSemifield.{0} E inst)))
        (@NumberField.RingOfIntegers.instAlgebra_1.{0} E inst))
      (@SMulZeroClass.toSMul.{0, 0} E V
        (@AddZero.toZero.{0} V
          (@AddZeroClass.toAddZero.{0} V
            (@AddMonoid.toAddZeroClass.{0} V
              (@SubNegMonoid.toAddMonoid.{0} V
                (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))))
        (@DistribSMul.toSMulZeroClass.{0, 0} E V
          (@AddMonoid.toAddZeroClass.{0} V
            (@SubNegMonoid.toAddMonoid.{0} V (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))
          (@DistribMulAction.toDistribSMul.{0, 0} E V
            (@Semiring.toMonoid.{0} E
              (@DivisionSemiring.toSemiring.{0} E
                (@Semifield.toDivisionSemiring.{0} E (@Field.toSemifield.{0} E inst))))
            (@SubNegMonoid.toAddMonoid.{0} V (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2)))
            (@Module.toDistribMulAction.{0, 0} E V
              (@DivisionSemiring.toSemiring.{0} E (@Semifield.toDivisionSemiring.{0} E (@Field.toSemifield.{0} E inst)))
              (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_3))))
      (@SMulZeroClass.toSMul.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
        (@AddZero.toZero.{0} V
          (@AddZeroClass.toAddZero.{0} V
            (@AddMonoid.toAddZeroClass.{0} V
              (@SubNegMonoid.toAddMonoid.{0} V
                (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))))
        (@DistribSMul.toSMulZeroClass.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
          (@AddMonoid.toAddZeroClass.{0} V
            (@SubNegMonoid.toAddMonoid.{0} V (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))
          (@DistribMulAction.toDistribSMul.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
            (@Semiring.toMonoid.{0} (@NumberField.RingOfIntegers.{0} E inst)
              (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                  (@NumberField.instCommRingRingOfIntegers.{0} E inst))))
            (@SubNegMonoid.toAddMonoid.{0} V (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2)))
            (@Module.toDistribMulAction.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
              (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                  (@NumberField.instCommRingRingOfIntegers.{0} E inst)))
              (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4))))]
  (Λ :
    @Submodule.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
      (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
        (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
          (@NumberField.instCommRingRingOfIntegers.{0} E inst)))
      (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4),
  @Submodule.IsLattice.{0, 0, 0} (@NumberField.RingOfIntegers.{0} E inst)
      (@NumberField.instCommRingRingOfIntegers.{0} E inst) E (@Field.toCommRing.{0} E inst)
      (@NumberField.RingOfIntegers.instAlgebra_1.{0} E inst) V (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4
      inst_3 inst_5 inst_5 Λ →
    ∀ (v : V),
      @Exists.{1} Nat fun (m : Nat) ↦
        And (@Ne.{1} Nat m (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@Membership.mem.{0, 0} V
            (@Submodule.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
              (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                  (@NumberField.instCommRingRingOfIntegers.{0} E inst)))
              (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4)
            (@SetLike.instMembership.{0, 0}
              (@Submodule.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
                (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                  (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                    (@NumberField.instCommRingRingOfIntegers.{0} E inst)))
                (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4)
              V
              (@Submodule.setLike.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
                (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                  (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                    (@NumberField.instCommRingRingOfIntegers.{0} E inst)))
                (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4))
            Λ
            (@HSMul.hSMul.{0, 0, 0} E V V
              (@instHSMul.{0, 0} E V
                (@SMulZeroClass.toSMul.{0, 0} E V
                  (@AddZero.toZero.{0} V
                    (@AddZeroClass.toAddZero.{0} V
                      (@AddMonoid.toAddZeroClass.{0} V
                        (@SubNegMonoid.toAddMonoid.{0} V
                          (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))))
                  (@DistribSMul.toSMulZeroClass.{0, 0} E V
                    (@AddMonoid.toAddZeroClass.{0} V
                      (@SubNegMonoid.toAddMonoid.{0} V
                        (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))
                    (@DistribMulAction.toDistribSMul.{0, 0} E V
                      (@Semiring.toMonoid.{0} E
                        (@DivisionSemiring.toSemiring.{0} E
                          (@Semifield.toDivisionSemiring.{0} E (@Field.toSemifield.{0} E inst))))
                      (@SubNegMonoid.toAddMonoid.{0} V
                        (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2)))
                      (@Module.toDistribMulAction.{0, 0} E V
                        (@DivisionSemiring.toSemiring.{0} E
                          (@Semifield.toDivisionSemiring.{0} E (@Field.toSemifield.{0} E inst)))
                        (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_3)))))
              (@Nat.cast.{0} E
                (@AddMonoidWithOne.toNatCast.{0} E
                  (@AddGroupWithOne.toAddMonoidWithOne.{0} E
                    (@Ring.toAddGroupWithOne.{0} E (@DivisionRing.toRing.{0} E (@Field.toDivisionRing.{0} E inst)))))
                m)
              v)) := by sorry
