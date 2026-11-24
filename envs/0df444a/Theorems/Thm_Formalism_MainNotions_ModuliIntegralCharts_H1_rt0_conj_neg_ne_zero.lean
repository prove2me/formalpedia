-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_rt0_conj_neg_ne_zero
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.rt0_conj_neg_ne_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:02:40.612828+00:00
-- url     : https://prove2.me/theorems/9e97e1e3-8a4e-495c-824a-b7db73b9ee3a
-- title:
--   H1: rt0 conj neg ne zero
-- statement:
--   The H1 construction uses the rt0 conj neg ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PsiCover.lean#L13-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PsiCover.lean#L13-L29

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndEnc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PsiCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by sorry
