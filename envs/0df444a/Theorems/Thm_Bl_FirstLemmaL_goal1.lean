-- Prove2me | Theorems.Thm_Bl_FirstLemmaL_goal1
-- name    : Bl.FirstLemmaL.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:15.470073+00:00
-- url     : https://prove2.me/theorems/8a958d6c-cd20-4bc8-8940-d04af55a1d8d
-- title:
--   First Lemma L: goal1
-- statement:
--   The First Lemma L construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CapelliComplements/FirstLemmaL.lean#L5-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CapelliComplements/FirstLemmaL.lean#L5-L56

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CapelliComplements_FirstLemmaL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.FirstLemmaL

theorem Bl.FirstLemmaL.goal1 :
  ∀ {G : Type} [inst : Group.{0} G] [inst_1 : TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G]
  [LocallyCompactSpace.{0} G] [SecondCountableTopology.{0} G] [T2Space.{0} G] [inst_6 : MeasurableSpace.{0} G]
  [BorelSpace.{0} G] {μ : MeasureTheory.Measure.{0} G} [MeasureTheory.Measure.IsHaarMeasure.{0} μ] {φ : G → Complex},
  MeasureTheory.Integrable.{0, 0} φ μ →
    (∀ (w : G),
        Eq.{1}
          (MeasureTheory.integral.{0, 0} μ fun (y : G) ↦
            HMul.hMul.{0, 0, 0} (φ y) (φ (HMul.hMul.{0, 0, 0} (Inv.inv.{0} y) w)))
          (φ w)) →
      ∀ {F : G → Complex},
        Continuous.{0, 0} F →
          ∀ {M : Real},
            (∀ (y : G), LE.le.{0} (Norm.norm.{0} (F y)) M) →
              Eq.{1}
                (MeasureTheory.integral.{0, 0} μ fun (y : G) ↦
                  HMul.hMul.{0, 0, 0} (φ y)
                    (MeasureTheory.integral.{0, 0} μ fun (z : G) ↦
                      HMul.hMul.{0, 0, 0} (φ z) (F (HMul.hMul.{0, 0, 0} y z))))
                (MeasureTheory.integral.{0, 0} μ fun (w : G) ↦ HMul.hMul.{0, 0, 0} (φ w) (F w)) := by sorry
