-- Prove2me | Theorems.Thm_Formalism_L2_NCov_length_quot_map
-- name    : Formalism.L2.NCov.length_quot_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:40.223564+00:00
-- url     : https://prove2.me/theorems/73305a3d-f742-4dab-98ee-3ce8692e7c4a
-- title:
--   NCov: length quot map
-- statement:
--   The NCov construction uses the length quot map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverLen.lean#L38-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverLen.lean#L38-L62

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

theorem Formalism.L2.NCov.length_quot_map (φ : R ≃+* R') (f : M →ₛₗ[(φ : R →+* R')] M') (hf : Function.Injective f)
    (p q : Submodule R M) :
    haveI := RingHomInvPair.of_ringEquiv φ
    Module.length R' (↥(p.map f) ⧸ (q.map f).comap (p.map f).subtype) =
      Module.length R (↥p ⧸ q.comap p.subtype) := by sorry
