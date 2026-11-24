-- Prove2me | Theorems.Thm_Formalism_MainNotions_GlobalTheoryTheory_GenusMassVolumes_SelfDual_eq_of_test
-- name    : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual.eq_of_test
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:08.448479+00:00
-- url     : https://prove2.me/theorems/d3391fc8-7885-4234-8853-ef86bf221746
-- title:
--   Self Dual: eq of test
-- statement:
--   The Self Dual construction uses the eq of test property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/GenusMassVolumes.lean#L138-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GlobalSchurBounds/GeneralLinearActions/GenusMassVolumes.lean#L138-L170

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology

theorem Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.SelfDual.eq_of_test {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] {μ ν : Measure V} {χ : V → V → ℂ}
    (hμ : SelfDual μ χ) (hν : SelfDual ν χ) (Φ : V → ℂ) (hc : Continuous Φ)
    (hs : HasCompactSupport Φ) (hI : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ)
    (z : V) (hz : Φ (-z) ≠ 0) : ν = μ := by sorry
