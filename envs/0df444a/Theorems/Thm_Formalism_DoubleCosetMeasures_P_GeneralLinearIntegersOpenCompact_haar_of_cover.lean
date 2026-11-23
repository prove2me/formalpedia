-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_GeneralLinearIntegersOpenCompact_haar_of_cover
-- name    : Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.haar_of_cover
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:33.761631+00:00
-- url     : https://prove2.me/theorems/0a49c643-d3e3-43aa-b672-8838c14cd93f
-- title:
--   General Linear Integers Open Compact: haar of cover
-- statement:
--   The General Linear Integers Open Compact construction uses the haar of cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsClosedLowUni.lean#L11-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/IsClosedLowUni.lean#L11-L45

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GLRealOpen
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GlR
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsClosedLowUni
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact

theorem Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.haar_of_cover {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (K₁ : Subgroup G) (hKo : IsOpen (K₁ : Set G))
    (hKc : IsCompact (K₁ : Set G)) (L : ℕ → Subgroup G) (hLo : ∀ m, IsOpen (L m : Set G))
    (hLc : ∀ m, IsCompact (L m : Set G)) (hcov : ∀ g : G, ∃ m, g ∈ L m) :
    ∃ μ : Measure G, μ.IsMulLeftInvariant ∧ μ.IsMulRightInvariant ∧ SFinite μ ∧
      μ (K₁ : Set G) = 1 := by sorry
