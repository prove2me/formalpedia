-- Prove2me | Theorems.Thm_Formalism_L2_Pj_lawA13_of_continuous
-- name    : Formalism.L2.Pj.lawA13_of_continuous
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:19:47.576795+00:00
-- url     : https://prove2.me/theorems/38ae9b22-771a-4dfb-ad95-c995adb430b0
-- title:
--   Pj: law A13 of continuous
-- statement:
--   The Pj construction uses the law A13 of continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LawA13OfContinuous.lean#L24-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LawA13OfContinuous.lean#L24-L31

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CompHt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LawA13OfContinuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open MeasureTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)]
variable (d : Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z))

theorem Formalism.L2.Pj.lawA13_of_continuous (hc : A13ContinuousOffNull d) : A13Measurable d := by sorry
