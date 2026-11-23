-- Prove2me | Theorems.Thm_Bl_CyclicComponents_goal1
-- name    : Bl.CyclicComponents.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:28:47.115694+00:00
-- url     : https://prove2.me/theorems/c383c670-11fa-4577-9a57-e0c45967e715
-- title:
--   Cyclic Components: goal1
-- statement:
--   The Cyclic Components construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/TwistedIdempotents/TwistedIdem.lean#L98-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/TwistedIdempotents/TwistedIdem.lean#L98-L168

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_PropositionOneCentralCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleProbSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaLWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartEqIff
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartSpec
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaP
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdemSelfAdjoint
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSquarefreeCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRTypeCountExact
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleTypeProb
import Definitions.Def_Lemmata_TwistedIdempotents_TwistedIdem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.CyclicComponents

theorem Bl.CyclicComponents.goal1 :
  ∀ {G : Type} [inst : Group.{0} G] [inst_1 : Fintype.{0} G] {V : Type} [inst_2 : AddCommGroup.{0} V]
  [inst_3 : Module.{0, 0} Complex V] [FiniteDimensional.{0, 0} Complex V] (ρ : Representation.{0, 0, 0} Complex G V)
  (J : Subgroup.{0} G) (χ : MonoidHom.{0, 0} (Subtype.{1} fun (x : G) ↦ Membership.mem.{0, 0} J x) (Units.{0} Complex)),
  (∀ (g g' : G),
      Eq.{1}
        (HMul.hMul.{0, 0, 0}
          (HMul.hMul.{0, 0, 0}
            (HMul.hMul.{0, 0, 0} (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ)
              (DFunLike.coe.{1, 1, 1} (MonoidAlgebra.of.{0, 0} Complex G) g))
            (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ))
          (HMul.hMul.{0, 0, 0}
            (HMul.hMul.{0, 0, 0} (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ)
              (DFunLike.coe.{1, 1, 1} (MonoidAlgebra.of.{0, 0} Complex G) g'))
            (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ)))
        (HMul.hMul.{0, 0, 0}
          (HMul.hMul.{0, 0, 0}
            (HMul.hMul.{0, 0, 0} (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ)
              (DFunLike.coe.{1, 1, 1} (MonoidAlgebra.of.{0, 0} Complex G) g'))
            (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ))
          (HMul.hMul.{0, 0, 0}
            (HMul.hMul.{0, 0, 0} (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ)
              (DFunLike.coe.{1, 1, 1} (MonoidAlgebra.of.{0, 0} Complex G) g))
            (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.twistedIdem J χ)))) →
    Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.IsIrr ρ →
      LE.le.{0}
        (Module.finrank.{0, 0} Complex
          (Subtype.{1} fun (x : V) ↦
            Membership.mem.{0, 0}
              (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.eqvSpace ρ
                (fun (u : Subtype.{1} fun (x : G) ↦ Membership.mem.{0, 0} J x) ↦ Subtype.val.{1} u)
                fun (u : Subtype.{1} fun (x : G) ↦ Membership.mem.{0, 0} J x) ↦
                Units.val.{0} (DFunLike.coe.{1, 1, 1} χ u))
              x))
        1 := by sorry
