-- Prove2me | Theorems.Thm_Formalism_L2_Pj_evalAt_one
-- name    : Formalism.L2.Pj.evalAt_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:04.490777+00:00
-- url     : https://prove2.me/theorems/3fbba711-0019-4d22-bf5e-fa57f8b36376
-- title:
--   Pj: eval At one
-- statement:
--   The Pj construction uses the eval At one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AlgebraMapCAt.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/AlgebraMapCAt.lean#L75-L77

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

theorem Formalism.L2.Pj.evalAt_one {S : Type} [CommRing S] [Algebra K S] (y : pts S) (h : FromTest pts mapR y) :
    evalAt pts mapR (1 : Rules pts) y = 1 := by sorry
