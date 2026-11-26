-- Prove2me | Theorems.Thm_EtaRepeatsTilde
-- name    : EtaRepeatsTilde
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:00:05.54719+00:00
-- url     : https://prove2.me/theorems/757c4d60-be97-59a8-bf1f-81b06842f42b
-- title:
--   Eta Repeats Tilde: Eta Repeats Tilde
-- statement:
--   The Eta Repeats Tilde construction uses the Eta Repeats Tilde property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/EtaRepeatsTilde.lean#L16-L117
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/EtaRepeatsTilde.lean#L16-L117

import Definitions.Def_Tablet_psiTilde
import Definitions.Def_Tablet_PSFamily
import Definitions.Def_Tablet_CurveLenMeasurable
import Definitions.Def_Tablet_CurveRestrictTotAgrees
import Definitions.Def_Tablet_CurveScaledEvalMeasurable
import Definitions.Def_Tablet_CurveRestrictTotMeasurable
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_EtaRepeats
import Definitions.Def_Tablet_PsiReindex
import Definitions.Def_Tablet_PsiReindexTilde
import Definitions.Def_Tablet_PsiTildeMeasurable
import Definitions.Def_Tablet_EtaRepeatsTilde
import Theorems.Thm_CurveLenMeasurable
import Theorems.Thm_CurveRestrictTotAgrees
import Theorems.Thm_CurveRestrictTotMeasurable
import Theorems.Thm_CurveScaledEvalMeasurable
import Theorems.Thm_EtaRepeats
import Theorems.Thm_PsiReindex
import Theorems.Thm_PsiReindexTilde
import Theorems.Thm_PsiTildeMeasurable

set_option autoImplicit false
open MeasureTheory

theorem EtaRepeatsTilde {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : Form1 E → ℝ) (F : PSFamily T)
    (m : ℕ) (hm : 0 < m) (Q : Finset E) (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C)
    (l : ℕ) (hl : 0 < l) :
    ∫ γ, (l : ℝ)⁻¹ * psiTilde (m * l) Q ε C γ ∂(F.eta l)
      = ∫ γ, psiTilde m Q ε C γ ∂(F.eta 1) := by sorry
