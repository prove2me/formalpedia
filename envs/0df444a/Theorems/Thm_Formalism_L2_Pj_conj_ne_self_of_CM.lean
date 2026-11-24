-- Prove2me | Theorems.Thm_Formalism_L2_Pj_conj_ne_self_of_CM
-- name    : Formalism.L2.Pj.conj_ne_self_of_CM
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:56.452069+00:00
-- url     : https://prove2.me/theorems/c7a41a60-b2ce-466d-af47-ff1263bd551f
-- title:
--   Pj: conj ne self of CM
-- statement:
--   The Pj construction uses the conj ne self of CM property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ConjNeSelfOfCM.lean#L31-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ConjNeSelfOfCM.lean#L31-L36

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeOrd
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeDiv
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ConjNeSelfOfCM
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
open Formalism Formalism.L2 Formalism.L2.Pj
open MvPowerSeries NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} [StarRing (𝓞 E)]
omit [StarRing (𝓞 E)]

theorem Formalism.L2.Pj.conj_ne_self_of_CM (τ : E →+* ℂ) : ComplexEmbedding.conjugate τ ≠ τ := by sorry
