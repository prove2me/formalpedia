-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PBD_lpt_value_nonneg_of_pos_of_size_le
-- name    : Formalism.FourierDecayAlt.P.PBD.lpt_value_nonneg_of_pos_of_size_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:33:03.749348+00:00
-- url     : https://prove2.me/theorems/06a3bb69-1cd2-4395-b3ed-b37712859ff4
-- title:
--   PBD: lpt value nonneg of pos of size le
-- statement:
--   The PBD construction uses the lpt value nonneg of pos of size le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L195-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ComponentFamilySettingOfSettingBis.lean#L195-L208

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem Formalism.FourierDecayAlt.P.PBD.lpt_value_nonneg_of_pos_of_size_le (k r : ℕ) (GG : ℝ) (fr : ℕ → ℕ → ℝ) (hfr : ∀ b s, 0 < fr b s) :
    ∀ (p : C.LPt) (b : ℕ), 1 ≤ b → b + D.ptSize p ≤ r + 1 → 0 ≤ C.nAux k r GG fr b p
  := by sorry
