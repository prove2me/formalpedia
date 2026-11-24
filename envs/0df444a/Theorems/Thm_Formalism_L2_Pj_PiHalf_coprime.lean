-- Prove2me | Theorems.Thm_Formalism_L2_Pj_PiHalf_coprime
-- name    : Formalism.L2.Pj.PiHalf.coprime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T03:58:14.688607+00:00
-- url     : https://prove2.me/theorems/d00beaae-79a6-4746-9e4b-d58d851d00fe
-- title:
--   Pi Half: coprime
-- statement:
--   The Pi Half construction uses the coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DepthPins.lean#L13-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DepthPins.lean#L13-L26

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DepthPins
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

theorem Formalism.L2.Pj.PiHalf.coprime {l : Level H} {D : DepData E} (h : PiHalf l D) (i k : Fin 2) :
    IsCoprime (D.pi i) (H.bar (D.pi k)) := by sorry
