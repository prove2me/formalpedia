-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_toStd_ok_iff
-- name    : Formalism.FourierDecayAlt.P.PBD.toStd_ok_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:33:33.257739+00:00
-- url     : https://prove2.me/theorems/734ba7fb-a608-41c6-953f-6eedcd61a2ba
-- title:
--   PBD: to Std ok iff
-- statement:
--   The PBD construction uses the to Std ok iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L25-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L25-L40

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ComponentFamilySettingOfSettingBis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBD
open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants
open scoped Matrix

theorem Formalism.FourierDecayAlt.P.PBD.toStd_ok_iff (r : ℕ) (g : ℝ) (hg : 0 < g) : ∀ (p : C.LPt) (b : ℕ),
    (∀ x ∈ D.toStd r g b p, 1 ≤ x.1 ∧ x.2 ≠ 0) ↔ ∀ x ∈ p, 1 ≤ x.1 ∧ x.2 ≠ 0
  := by sorry
