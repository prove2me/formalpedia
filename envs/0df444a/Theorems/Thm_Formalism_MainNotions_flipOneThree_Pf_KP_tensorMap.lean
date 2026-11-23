-- Prove2me | Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_KP_tensorMap
-- name    : Formalism.MainNotions.flipOneThree.Pf.KP.tensorMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:54:50.764154+00:00
-- url     : https://prove2.me/theorems/641dc36b-c0ab-4c72-8c33-033b7bea6419
-- title:
--   KP: tensor Map
-- statement:
--   The KP construction uses the tensor Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/TensorKP.lean#L20-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/TensorKP.lean#L20-L50

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_TensorKP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.KP

theorem Formalism.MainNotions.flipOneThree.Pf.KP.tensorMap {K : Type} [Field K] {S α B : Type} [Fintype S] [DecidableEq S] [CommRing B]
    [Algebra K B] (g : S → MvPolynomial α K →ₗ[K] B) :
    ∃ F : MvPolynomial (S × α) K →ₗ[K] B, ∀ P : S → MvPolynomial α K,
      F (∏ s, rename (fun v => (s, v)) (P s)) = ∏ s, g s (P s) := by sorry
