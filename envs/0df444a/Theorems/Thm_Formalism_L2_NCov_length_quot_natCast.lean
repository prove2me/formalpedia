-- Prove2me | Theorems.Thm_Formalism_L2_NCov_length_quot_natCast
-- name    : Formalism.L2.NCov.length_quot_natCast
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:43.458718+00:00
-- url     : https://prove2.me/theorems/206d2767-55fe-4669-86fe-99d20ff7509d
-- title:
--   NCov: length quot nat Cast
-- statement:
--   The NCov construction uses the length quot nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverLen.lean#L64-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverLen.lean#L64-L78

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

theorem Formalism.L2.NCov.length_quot_natCast (φ : R ≃+* R') (n : ℕ) :
    Module.length R' (R' ⧸ Ideal.span {(n : R')}) = Module.length R (R ⧸ Ideal.span {(n : R)}) := by sorry
