-- Prove2me | Theorems.Thm_Formalism_L2_Pj_embK_coe
-- name    : Formalism.L2.Pj.embK_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:17:23.307264+00:00
-- url     : https://prove2.me/theorems/12aff898-30c0-4534-8505-0f913a0bfc33
-- title:
--   Pj: emb K coe
-- statement:
--   The Pj construction uses the emb K coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/EmbKCoe.lean#L33-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/EmbKCoe.lean#L33-L33

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_EmbKCoe
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
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {l : Level H} (c : Coeff l)

theorem Formalism.L2.Pj.embK_coe (τ : E →+* ℂ) (a : 𝓞 E) : ((embK c τ a : c.F) : ℂ) = τ (a : E) := by sorry
