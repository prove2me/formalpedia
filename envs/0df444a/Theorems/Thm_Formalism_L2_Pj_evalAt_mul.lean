-- Prove2me | Theorems.Thm_Formalism_L2_Pj_evalAt_mul
-- name    : Formalism.L2.Pj.evalAt_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:52.65309+00:00
-- url     : https://prove2.me/theorems/b55f68aa-f916-4006-86a2-0bd6f4f97570
-- title:
--   Pj: eval At mul
-- statement:
--   The Pj construction uses the eval At mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AlgebraMapCAt.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AlgebraMapCAt.lean#L71-L73

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
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
open MvPolynomial
variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)

theorem Formalism.L2.Pj.evalAt_mul (f g : Rules pts) {S : Type} [CommRing S] [Algebra K S] (y : pts S) :
    evalAt pts mapR (f * g) y = evalAt pts mapR f y * evalAt pts mapR g y := by sorry
