-- Prove2me | Theorems.Thm_Formalism_L2_Pj_hkOp_spec
-- name    : Formalism.L2.Pj.hkOp_spec
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:47:14.33511+00:00
-- url     : https://prove2.me/theorems/a784ae3c-b703-5c5c-a951-73c3c65def5d
-- title:
--   Pj: hk Op spec
-- statement:
--   The Pj construction uses the hk Op spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/HeckeStabSet.lean#L111-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/HeckeStabSet.lean#L111-L113

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RhoWApply
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_HeckeStabSet
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
variable (hkIdx : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω], pts Ω → Type)
variable (quotR : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (y : pts Ω), hkIdx Ω y → pts Ω → Prop)
variable {pts mapR borR hkIdx quotR}

theorem Formalism.L2.Pj.hkOp_spec [Fintype ι] {e : ι → ℕ} {c : K} (hE : HkEx pts mapR borR hkIdx quotR e c)
    (hD : PtsDetect pts mapR borR e) (hF : HkFin pts hkIdx) (f : secW pts mapR borR e) :
    HkRel pts mapR hkIdx quotR c f (hkOp hE hD hF f) := by sorry
