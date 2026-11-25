-- Prove2me | Theorems.Thm_Formalism_L2_Pj_actL_apply
-- name    : Formalism.L2.Pj.actL_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:46:20.944749+00:00
-- url     : https://prove2.me/theorems/2644c1d1-9545-41a0-a8e7-b3dd5642c392
-- title:
--   Pj: act L apply
-- statement:
--   The Pj construction uses the act L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RhoWApply.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RhoWApply.lean#L27-L28

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RhoWApply
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
variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
variable {G : Type} [Group G]
variable (actR : ∀ {S : Type} [CommRing S] [Algebra K S], G → pts S → pts S → Prop)

theorem Formalism.L2.Pj.actL_apply (g : G) (f : Rules pts) (p : TRing K) (y : pts p.R) :
    actL pts actR g f p y = f p (mvPt pts actR g y) := by sorry
