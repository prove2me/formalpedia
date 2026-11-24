-- Prove2me | Theorems.Thm_Formalism_L2_NCov_pow_sub_apply_eq_zero
-- name    : Formalism.L2.NCov.pow_sub_apply_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:42.874709+00:00
-- url     : https://prove2.me/theorems/5f32b547-a440-437a-825d-3c0ef755a4bb
-- title:
--   NCov: pow sub apply eq zero
-- statement:
--   The NCov construction uses the pow sub apply eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L323-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L323-L330

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
open Polynomial
variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [IsLocalRing O]
  {S : Set (End K V)}

theorem Formalism.L2.NCov.pow_sub_apply_eq_zero [FiniteDimensional K V] (ψ : Algebra.adjoin O S →ₐ[O] O)
    (t : Algebra.adjoin O S) {x : V} (hx : x ∈ W _ (pt ψ)) :
    (((t : End K V) - algebraMap O (End K V) (ψ t)) ^
      ((t : End K V).maxGenEigenspaceIndex (pt ψ t))) x = 0 := by sorry
