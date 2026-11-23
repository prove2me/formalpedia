-- Prove2me | Theorems.Thm_Formalism_L2_NCov_length_eq_of_bijective
-- name    : Formalism.L2.NCov.length_eq_of_bijective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:28.457861+00:00
-- url     : https://prove2.me/theorems/aededb2c-8be3-4717-8928-240e1a2031c6
-- title:
--   NCov: length eq of bijective
-- statement:
--   The NCov construction uses the length eq of bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverLen.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverLen.lean#L12-L18

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverLen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.NCov
open Module
variable {R R' M M' : Type*} [CommRing R] [CommRing R'] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R' M']

theorem Formalism.L2.NCov.length_eq_of_bijective (φ : R ≃+* R') (f : M →ₛₗ[(φ : R →+* R')] M') (hf : Function.Bijective f) :
    Module.length R' M' = Module.length R M := by sorry
