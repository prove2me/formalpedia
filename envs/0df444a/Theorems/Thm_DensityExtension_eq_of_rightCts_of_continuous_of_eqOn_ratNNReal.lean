-- Prove2me | Theorems.Thm_DensityExtension_eq_of_rightCts_of_continuous_of_eqOn_ratNNReal
-- name    : DensityExtension.eq_of_rightCts_of_continuous_of_eqOn_ratNNReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:37:06.096743+00:00
-- url     : https://prove2.me/theorems/bdf71d6d-e877-4b0d-9123-7c5e4ecfbd0a
-- title:
--   LeanLevy: DensityExtension.eq_of_rightCts_of_continuous_of_eqOn_ratNNReal
-- statement:
--   If `f` is right-continuous, `g` is continuous, both from `ℝ≥0` to a T₂ space, and Exact extracted Lean theorem type; proof pending Prove2Me verification.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L180

import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Normed.Module.Connected

universe u_1
theorem DensityExtension.eq_of_rightCts_of_continuous_of_eqOn_ratNNReal : ∀ {β : Type u_1} [inst : TopologicalSpace β] [@T2Space β inst] {f g : NNReal → β},
  (∀ (t : NNReal),
      @ContinuousWithinAt NNReal β NNReal.instTopologicalSpace inst f
        (@Set.Ici NNReal (@PartialOrder.toPreorder NNReal NNReal.instPartialOrder) t) t) →
    @Continuous NNReal β NNReal.instTopologicalSpace inst g →
      (∀ (k n : Nat),
          @Eq β
            (f
              (@HDiv.hDiv NNReal NNReal NNReal (@instHDiv NNReal NNReal.instDiv)
                (@Nat.cast NNReal
                  (@AddMonoidWithOne.toNatCast NNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne NNReal
                      (@NonAssocSemiring.toAddCommMonoidWithOne NNReal
                        (@Semiring.toNonAssocSemiring NNReal NNReal.instSemiring))))
                  k)
                (@Nat.cast NNReal
                  (@AddMonoidWithOne.toNatCast NNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne NNReal
                      (@NonAssocSemiring.toAddCommMonoidWithOne NNReal
                        (@Semiring.toNonAssocSemiring NNReal NNReal.instSemiring))))
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            (g
              (@HDiv.hDiv NNReal NNReal NNReal (@instHDiv NNReal NNReal.instDiv)
                (@Nat.cast NNReal
                  (@AddMonoidWithOne.toNatCast NNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne NNReal
                      (@NonAssocSemiring.toAddCommMonoidWithOne NNReal
                        (@Semiring.toNonAssocSemiring NNReal NNReal.instSemiring))))
                  k)
                (@Nat.cast NNReal
                  (@AddMonoidWithOne.toNatCast NNReal
                    (@AddCommMonoidWithOne.toAddMonoidWithOne NNReal
                      (@NonAssocSemiring.toAddCommMonoidWithOne NNReal
                        (@Semiring.toNonAssocSemiring NNReal NNReal.instSemiring))))
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))) →
        @Eq (NNReal → β) f g := by sorry
