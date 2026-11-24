-- Prove2me | Theorems.Thm_Formalism_L2_NCov_add_pow_apply_eq_zero
-- name    : Formalism.L2.NCov.add_pow_apply_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:48.082237+00:00
-- url     : https://prove2.me/theorems/ed7f40d0-3c9b-41d6-bff9-c2e1b07af4fa
-- title:
--   NCov: add pow apply eq zero
-- statement:
--   The NCov construction uses the add pow apply eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L14-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L14-L26

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.NCov
open Module Module.End
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem Formalism.L2.NCov.add_pow_apply_eq_zero {P Q : End K V} (h : Commute P Q) {x : V} {k l : ℕ}
    (hP : (P ^ k) x = 0) (hQ : (Q ^ l) x = 0) : ((P + Q) ^ (k + l)) x = 0 := by sorry
