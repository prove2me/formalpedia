-- Prove2me | Theorems.Thm_Bl_ClearingDenominators_goal1
-- name    : Bl.ClearingDenominators.goal1
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:35:57.026851+00:00
-- url     : https://prove2.me/theorems/62353f62-1dea-46d8-91af-202fbfdba287
-- title:
--   Clearing Denominators: goal1
-- statement:
--   The Clearing Denominators construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/ClearingDenominators/UmonLeUzmon.lean#L103-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/ClearingDenominators/UmonLeUzmon.lean#L103-L257

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ObjPol
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalRingCardinality_DataKernels
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_DataS
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitsPlaces
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitCountSg
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Definitions.Def_Formalism_CoboundaryTransfers_Statement
import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_FrameTransport
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_Point
import Definitions.Def_Formalism_TameInertiaTowers_FinalGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_Galois
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_ConjEqInvOfPowEqOne
import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantCompactSpan
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantOrthogonalInf
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FirstSlotSliceSlotMixedCasimirZero
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementD
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuadraticInequalityBoundHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_SumOfSquaresIdentityHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CasKHW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HWDiag
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_TrPowSumFilterZero
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnG
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementA
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementC
import Definitions.Def_Lemmata_ClearingDenominators_UmonLeUzmon
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open Bl Bl.ClearingDenominators

theorem Bl.ClearingDenominators.goal1 :
  ∀ {n : Nat} {O : Type u_1} [inst : CommRing.{u_1} O]
  [inst_1 : @IsDomain.{u_1} O (@CommSemiring.toSemiring.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst))]
  [@IsDiscreteValuationRing.{u_1} O inst inst_1] {V : Type u_2} [inst_3 : AddCommGroup.{u_2} V]
  [inst_4 :
    @Module.{u_1, u_2} (@Formalism.MainNotions.G.KK.{u_1} O inst inst_1) V
      (@OreLocalization.instSemiring.{u_1} O (@CommSemiring.toSemiring.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst))
        (@nonZeroDivisors.{u_1} O
          (@Semiring.toMonoidWithZero.{u_1} O
            (@CommSemiring.toSemiring.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst))))
        (@OreLocalization.oreSetComm.{u_1} O (@CommRing.toCommMonoid.{u_1} O inst)
          (@nonZeroDivisors.{u_1} O
            (@Semiring.toMonoidWithZero.{u_1} O
              (@CommSemiring.toSemiring.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst))))))
      (@AddCommGroup.toAddCommMonoid.{u_2} V inst_3)]
  [inst_5 :
    @Module.{u_1, u_2} O V (@CommSemiring.toSemiring.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst))
      (@AddCommGroup.toAddCommMonoid.{u_2} V inst_3)]
  [inst_6 :
    @IsScalarTower.{u_1, u_1, u_2} O (@Formalism.MainNotions.G.KK.{u_1} O inst inst_1) V
      (@OreLocalization.instSMulOfIsScalarTower.{u_1, u_1, u_1} O O O
        (@CommMonoid.toMonoid.{u_1} O (@CommRing.toCommMonoid.{u_1} O inst))
        (@nonZeroDivisors.{u_1} O
          (@Semiring.toMonoidWithZero.{u_1} O
            (@CommSemiring.toSemiring.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst))))
        (@OreLocalization.oreSetComm.{u_1} O (@CommRing.toCommMonoid.{u_1} O inst)
          (@nonZeroDivisors.{u_1} O
            (@Semiring.toMonoidWithZero.{u_1} O
              (@CommSemiring.toSemiring.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst)))))
        (@Monoid.toMulAction.{u_1} O (@CommMonoid.toMonoid.{u_1} O (@CommRing.toCommMonoid.{u_1} O inst)))
        (@instSMulOfMul.{u_1} O
          (@Distrib.toMul.{u_1} O
            (@instDistribOfSemiring.{u_1} O
              (@CommSemiring.toSemiring.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst)))))
        (@instSMulOfMul.{u_1} O
          (@Distrib.toMul.{u_1} O
            (@instDistribOfSemiring.{u_1} O
              (@CommSemiring.toSemiring.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst)))))
        _ _)
      (@SMulZeroClass.toSMul.{u_1, u_2} (@Formalism.MainNotions.G.KK.{u_1} O inst inst_1) V
        (@AddZero.toZero.{u_2} V
          (@AddZeroClass.toAddZero.{u_2} V
            (@AddMonoid.toAddZeroClass.{u_2} V
              (@SubNegMonoid.toAddMonoid.{u_2} V
                (@AddGroup.toSubNegMonoid.{u_2} V (@AddCommGroup.toAddGroup.{u_2} V inst_3))))))
        (@DistribSMul.toSMulZeroClass.{u_1, u_2} (@Formalism.MainNotions.G.KK.{u_1} O inst inst_1) V
          (@AddMonoid.toAddZeroClass.{u_2} V
            (@SubNegMonoid.toAddMonoid.{u_2} V
              (@AddGroup.toSubNegMonoid.{u_2} V (@AddCommGroup.toAddGroup.{u_2} V inst_3))))
          (@DistribMulAction.toDistribSMul.{u_1, u_2} (@Formalism.MainNotions.G.KK.{u_1} O inst inst_1) V
            (@OreLocalization.instMonoid.{u_1} O (@CommMonoid.toMonoid.{u_1} O (@CommRing.toCommMonoid.{u_1} O inst))
              (@nonZeroDivisors.{u_1} O
                (@Semiring.toMonoidWithZero.{u_1} O
                  (@CommSemiring.toSemiring.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst))))
              (@OreLocalization.oreSetComm.{u_1} O (@CommRing.toCommMonoid.{u_1} O inst)
                (@nonZeroDivisors.{u_1} O
                  (@Semiring.toMonoidWithZero.{u_1} O
                    (@CommSemiring.toSemiring.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst))))))
            (@SubNegMonoid.toAddMonoid.{u_2} V
              (@AddGroup.toSubNegMonoid.{u_2} V (@AddCommGroup.toAddGroup.{u_2} V inst_3)))
            (@Module.toDistribMulAction.{u_1, u_2} (@Formalism.MainNotions.G.KK.{u_1} O inst inst_1) V
              (@OreLocalization.instSemiring.{u_1} O
                (@CommSemiring.toSemiring.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst))
                (@nonZeroDivisors.{u_1} O
                  (@Semiring.toMonoidWithZero.{u_1} O
                    (@CommSemiring.toSemiring.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst))))
                (@OreLocalization.oreSetComm.{u_1} O (@CommRing.toCommMonoid.{u_1} O inst)
                  (@nonZeroDivisors.{u_1} O
                    (@Semiring.toMonoidWithZero.{u_1} O
                      (@CommSemiring.toSemiring.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst))))))
              (@AddCommGroup.toAddCommMonoid.{u_2} V inst_3) inst_4))))
      (@SMulZeroClass.toSMul.{u_1, u_2} O V
        (@AddZero.toZero.{u_2} V
          (@AddZeroClass.toAddZero.{u_2} V
            (@AddMonoid.toAddZeroClass.{u_2} V
              (@SubNegMonoid.toAddMonoid.{u_2} V
                (@AddGroup.toSubNegMonoid.{u_2} V (@AddCommGroup.toAddGroup.{u_2} V inst_3))))))
        (@DistribSMul.toSMulZeroClass.{u_1, u_2} O V
          (@AddMonoid.toAddZeroClass.{u_2} V
            (@SubNegMonoid.toAddMonoid.{u_2} V
              (@AddGroup.toSubNegMonoid.{u_2} V (@AddCommGroup.toAddGroup.{u_2} V inst_3))))
          (@DistribMulAction.toDistribSMul.{u_1, u_2} O V
            (@Semiring.toMonoid.{u_1} O (@CommSemiring.toSemiring.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst)))
            (@SubNegMonoid.toAddMonoid.{u_2} V
              (@AddGroup.toSubNegMonoid.{u_2} V (@AddCommGroup.toAddGroup.{u_2} V inst_3)))
            (@Module.toDistribMulAction.{u_1, u_2} O V
              (@CommSemiring.toSemiring.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst))
              (@AddCommGroup.toAddCommMonoid.{u_2} V inst_3) inst_5))))]
  {E :
    @Formalism.MainNotions.G.GLOps.{u_1, u_2} n (@Formalism.MainNotions.G.KK.{u_1} O inst inst_1) V (@FractionRing.field.{u_1} O inst inst_1) inst_3
      inst_4}
  {lam : Fin n → Int} {v : V},
  @Formalism.MainNotions.G.IsIrrHW.{u_1, u_2} n (@Formalism.MainNotions.G.KK.{u_1} O inst inst_1) V (@FractionRing.field.{u_1} O inst inst_1) inst_3
            inst_4 E lam v →
    ∀ (y : V),
      @Exists.{u_1 + 1} O fun (o : O) ↦
        And
          (@Ne.{u_1 + 1} O o
            (@OfNat.ofNat.{u_1} O (nat_lit 0)
              (@Zero.toOfNat0.{u_1} O
                (@MulZeroClass.toZero.{u_1} O
                  (@instMulZeroClassOfSemiring.{u_1} O
                    (@CommSemiring.toSemiring.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst)))))))
          (@Membership.mem.{u_2, u_2} V
            (@Submodule.{u_1, u_2} O V (@CommSemiring.toSemiring.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst))
              (@AddCommGroup.toAddCommMonoid.{u_2} V inst_3) inst_5)
            (@SetLike.instMembership.{u_2, u_2}
              (@Submodule.{u_1, u_2} O V (@CommSemiring.toSemiring.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst))
                (@AddCommGroup.toAddCommMonoid.{u_2} V inst_3) inst_5)
              V
              (@Submodule.setLike.{u_1, u_2} O V
                (@CommSemiring.toSemiring.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst))
                (@AddCommGroup.toAddCommMonoid.{u_2} V inst_3) inst_5))
            (@Formalism.MainNotions.G.Delta.{u_1, u_2, u_1} n (@Formalism.MainNotions.G.KK.{u_1} O inst inst_1) V
              (@FractionRing.field.{u_1} O inst inst_1) inst_3 inst_4 O inst inst_5
              (@OreLocalization.instAlgebra.{u_1, u_1} O
                (@CommSemiring.toSemiring.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst))
                (@nonZeroDivisors.{u_1} O
                  (@Semiring.toMonoidWithZero.{u_1} O
                    (@CommSemiring.toSemiring.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst))))
                (@OreLocalization.oreSetComm.{u_1} O (@CommRing.toCommMonoid.{u_1} O inst)
                  (@nonZeroDivisors.{u_1} O
                    (@Semiring.toMonoidWithZero.{u_1} O
                      (@CommSemiring.toSemiring.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst)))))
                O (@CommRing.toCommSemiring.{u_1} O inst) (@Algebra.id.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst)))
              inst_6 E v)
            (@HSMul.hSMul.{u_1, u_2, u_2} O V V
              (@instHSMul.{u_1, u_2} O V
                (@SMulZeroClass.toSMul.{u_1, u_2} O V
                  (@AddZero.toZero.{u_2} V
                    (@AddZeroClass.toAddZero.{u_2} V
                      (@AddMonoid.toAddZeroClass.{u_2} V
                        (@SubNegMonoid.toAddMonoid.{u_2} V
                          (@AddGroup.toSubNegMonoid.{u_2} V (@AddCommGroup.toAddGroup.{u_2} V inst_3))))))
                  (@DistribSMul.toSMulZeroClass.{u_1, u_2} O V
                    (@AddMonoid.toAddZeroClass.{u_2} V
                      (@SubNegMonoid.toAddMonoid.{u_2} V
                        (@AddGroup.toSubNegMonoid.{u_2} V (@AddCommGroup.toAddGroup.{u_2} V inst_3))))
                    (@DistribMulAction.toDistribSMul.{u_1, u_2} O V
                      (@Semiring.toMonoid.{u_1} O
                        (@CommSemiring.toSemiring.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst)))
                      (@SubNegMonoid.toAddMonoid.{u_2} V
                        (@AddGroup.toSubNegMonoid.{u_2} V (@AddCommGroup.toAddGroup.{u_2} V inst_3)))
                      (@Module.toDistribMulAction.{u_1, u_2} O V
                        (@CommSemiring.toSemiring.{u_1} O (@CommRing.toCommSemiring.{u_1} O inst))
                        (@AddCommGroup.toAddCommMonoid.{u_2} V inst_3) inst_5)))))
              o y)) := by sorry
