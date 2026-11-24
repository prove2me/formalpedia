-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_arcS_pin
-- name    : Formalism.L2.Pj.QAt.arcS_pin
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T20:08:07.558873+00:00
-- url     : https://prove2.me/theorems/61908969-c618-4acd-a1bc-2b92b0b8ae1f
-- title:
--   QAt: arc S pin
-- statement:
--   The QAt construction uses the arc S pin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/ArcLineFunctions/ArcSPin.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/ArcLineFunctions/ArcSPin.lean#L11-L22

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_ArcLineFunctions_ArcSPin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem Formalism.L2.Pj.QAt.arcS_pin (Dw : Datum H) (K₁ : Type) [Field K₁] {F₀ : Type} [Field F₀] [Algebra F₀ K₁] (r : F₀) :
    algebraMap F₀ (ArcS Dw K₁) r = arcι Dw K₁ (PowerSeries.C (R := K₁) (algebraMap F₀ K₁ r)) := by sorry
