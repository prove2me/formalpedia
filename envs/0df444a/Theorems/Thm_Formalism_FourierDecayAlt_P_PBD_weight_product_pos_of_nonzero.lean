-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_weight_product_pos_of_nonzero
-- name    : Formalism.FourierDecayAlt.P.PBD.weight_product_pos_of_nonzero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:35:24.530935+00:00
-- url     : https://prove2.me/theorems/bb9cf452-5bd6-5872-a925-5ddaad2dc07d
-- title:
--   PBD: weight product pos of nonzero
-- statement:
--   The PBD construction uses the weight product pos of nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L86-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L86-L103

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

theorem Formalism.FourierDecayAlt.P.PBD.weight_product_pos_of_nonzero (k r : ℕ) (GG : ℝ) (fr : ℕ → ℕ → ℝ) (hfr : ∀ b s, 0 < fr b s) :
    ∀ (p : C.LPt) (b : ℕ), 1 ≤ b → b + D.ptSize p ≤ r + 1 → (∀ x ∈ p, 1 ≤ x.1 ∧ x.2 ≠ 0) →
      0 < C.nAux k r GG fr b p
  := by sorry
