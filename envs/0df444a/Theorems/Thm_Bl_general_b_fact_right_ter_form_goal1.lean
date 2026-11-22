-- Prove2me | Theorems.Thm_Bl_general_b_fact_right_ter_form_goal1
-- name    : Bl.general_b_fact_right_ter_form.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:53.2838+00:00
-- url     : https://prove2.me/theorems/56239e99-1543-4802-9761-0fade8d29eda
-- title:
--   general b fact right ter form: goal1
-- statement:
--   The general b fact right ter form construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightTerForm/Imports.lean#L5-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightTerForm/Imports.lean#L5-L285

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightTerForm_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_right_ter_form

theorem Bl.general_b_fact_right_ter_form.goal1 :
  ∀ {L : Type} [inst : Field.{0} L] [inst_1 : @NumberField.{0} L inst] (x : L) (c : Int),
  @Eq.{1} L
      (@HPow.hPow.{0, 0, 0} L Nat L
        (@instHPow.{0, 0} L Nat
          (@NPow.toPow.{0} L
            (@Monoid.toNPow.{0} L
              (@Semiring.toMonoid.{0} L
                (@DivisionSemiring.toSemiring.{0} L
                  (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))))))
        x (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@Int.cast.{0} L
        (@AddGroupWithOne.toIntCast.{0} L
          (@Ring.toAddGroupWithOne.{0} L (@DivisionRing.toRing.{0} L (@Field.toDivisionRing.{0} L inst))))
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
            (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4)))
            (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) c))
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))) →
    ∀
      (P :
        @Ideal.{0} (@NumberField.RingOfIntegers.{0} L inst)
          (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
            (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
              (@NumberField.instCommRingRingOfIntegers.{0} L inst))))
      [hP :
        @Ideal.IsPrime.{0} (@NumberField.RingOfIntegers.{0} L inst)
          (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
            (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
              (@NumberField.instCommRingRingOfIntegers.{0} L inst)))
          P]
      [@Ideal.LiesOver.{0, 0} Int Int.instCommSemiring (@NumberField.RingOfIntegers.{0} L inst)
          (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
            (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
              (@NumberField.instCommRingRingOfIntegers.{0} L inst)))
          (@Ring.toIntAlgebra.{0} (@NumberField.RingOfIntegers.{0} L inst)
            (@CommRing.toRing.{0} (@NumberField.RingOfIntegers.{0} L inst)
              (@NumberField.instCommRingRingOfIntegers.{0} L inst)))
          P
          (@Ideal.span.{0} Int (@CommSemiring.toSemiring.{0} Int Int.instCommSemiring)
            (@Singleton.singleton.{0, 0} Int (Set.{0} Int) (@Set.instSingletonSet.{0} Int)
              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))]
      (σ :
        @AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
          (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
          (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
          (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
          (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)),
      @Membership.mem.{0, 0}
          (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
            (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
            (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
            (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
            (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
          (@Subgroup.{0}
            (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
              (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
              (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
              (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
              (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
            (@AlgEquiv.aut.{0, 0} Rat L Rat.commSemiring
              (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
              (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)))
          (@SetLike.instMembership.{0, 0}
            (@Subgroup.{0}
              (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
                (@DivisionSemiring.toSemiring.{0} L
                  (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                (@DivisionSemiring.toSemiring.{0} L
                  (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
                (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
              (@AlgEquiv.aut.{0, 0} Rat L Rat.commSemiring
                (@DivisionSemiring.toSemiring.{0} L
                  (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)))
            (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
              (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
              (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
              (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
              (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
            (@Subgroup.instSetLike.{0}
              (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
                (@DivisionSemiring.toSemiring.{0} L
                  (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                (@DivisionSemiring.toSemiring.{0} L
                  (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
                (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
              (@AlgEquiv.aut.{0, 0} Rat L Rat.commSemiring
                (@DivisionSemiring.toSemiring.{0} L
                  (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))))
          (@MulAction.stabilizer.{0, 0}
            (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
              (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
              (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
              (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
              (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
            (@Ideal.{0} (@NumberField.RingOfIntegers.{0} L inst)
              (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                  (@NumberField.instCommRingRingOfIntegers.{0} L inst))))
            (@AlgEquiv.aut.{0, 0} Rat L Rat.commSemiring
              (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
              (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
            (@DistribMulAction.toMulAction.{0, 0}
              (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
                (@DivisionSemiring.toSemiring.{0} L
                  (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                (@DivisionSemiring.toSemiring.{0} L
                  (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
                (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
              (@Ideal.{0} (@NumberField.RingOfIntegers.{0} L inst)
                (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                  (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                    (@NumberField.instCommRingRingOfIntegers.{0} L inst))))
              (@DivInvMonoid.toMonoid.{0}
                (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
                  (@DivisionSemiring.toSemiring.{0} L
                    (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                  (@DivisionSemiring.toSemiring.{0} L
                    (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                  (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
                  (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
                (@Group.toDivInvMonoid.{0}
                  (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
                    (@DivisionSemiring.toSemiring.{0} L
                      (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                    (@DivisionSemiring.toSemiring.{0} L
                      (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                    (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
                    (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
                  (@AlgEquiv.aut.{0, 0} Rat L Rat.commSemiring
                    (@DivisionSemiring.toSemiring.{0} L
                      (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                    (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))))
              (@AddMonoidWithOne.toAddMonoid.{0}
                (@Ideal.{0} (@NumberField.RingOfIntegers.{0} L inst)
                  (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                    (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                      (@NumberField.instCommRingRingOfIntegers.{0} L inst))))
                (@AddCommMonoidWithOne.toAddMonoidWithOne.{0}
                  (@Ideal.{0} (@NumberField.RingOfIntegers.{0} L inst)
                    (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                      (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                        (@NumberField.instCommRingRingOfIntegers.{0} L inst))))
                  (@Submodule.instAddCommMonoidWithOne.{0, 0} (@NumberField.RingOfIntegers.{0} L inst)
                    (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                      (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                        (@NumberField.instCommRingRingOfIntegers.{0} L inst)))
                    (@NumberField.RingOfIntegers.{0} L inst)
                    (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                      (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                        (@NumberField.instCommRingRingOfIntegers.{0} L inst)))
                    (@Semiring.toModule.{0} (@NumberField.RingOfIntegers.{0} L inst)
                      (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                        (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                          (@NumberField.instCommRingRingOfIntegers.{0} L inst)))))))
              (@Ideal.pointwiseDistribMulAction.{0, 0}
                (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
                  (@DivisionSemiring.toSemiring.{0} L
                    (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                  (@DivisionSemiring.toSemiring.{0} L
                    (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                  (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
                  (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
                (@NumberField.RingOfIntegers.{0} L inst)
                (@DivInvMonoid.toMonoid.{0}
                  (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
                    (@DivisionSemiring.toSemiring.{0} L
                      (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                    (@DivisionSemiring.toSemiring.{0} L
                      (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                    (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
                    (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
                  (@Group.toDivInvMonoid.{0}
                    (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
                      (@DivisionSemiring.toSemiring.{0} L
                        (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                      (@DivisionSemiring.toSemiring.{0} L
                        (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                      (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
                      (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
                    (@AlgEquiv.aut.{0, 0} Rat L Rat.commSemiring
                      (@DivisionSemiring.toSemiring.{0} L
                        (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                      (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))))
                (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                  (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                    (@NumberField.instCommRingRingOfIntegers.{0} L inst)))
                (@NumberField.RingOfIntegers.instMulSemiringAction.{0, 0} L inst
                  (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
                    (@DivisionSemiring.toSemiring.{0} L
                      (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                    (@DivisionSemiring.toSemiring.{0} L
                      (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                    (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
                    (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
                  (@AlgEquiv.aut.{0, 0} Rat L Rat.commSemiring
                    (@DivisionSemiring.toSemiring.{0} L
                      (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                    (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
                  (@AlgEquiv.applyMulSemiringAction.{0, 0} Rat L Rat.commSemiring
                    (@DivisionSemiring.toSemiring.{0} L
                      (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                    (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)))))
            P)
          σ →
        @Eq.{1} L
          (@DFunLike.coe.{1, 1, 1}
            (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
              (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
              (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
              (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
              (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
            L (fun (x : L) ↦ L)
            (@AlgEquiv.instFunLike.{0, 0, 0} Rat L L Rat.commSemiring
              (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
              (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
              (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
              (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
            σ x)
          x := by sorry
