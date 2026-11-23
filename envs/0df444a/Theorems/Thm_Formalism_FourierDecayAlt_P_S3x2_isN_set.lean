-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_isN_set
-- name    : Formalism.FourierDecayAlt.P.S3x2.isN_set
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:23.477681+00:00
-- url     : https://prove2.me/theorems/f7e9b30f-db4f-4441-b046-e0e3f5a6429c
-- title:
--   S3x2: is N set
-- statement:
--   The S3x2 construction uses the is N set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L294-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L294-L300

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReductionSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x2
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A] {r k : ℕ}

theorem Formalism.FourierDecayAlt.P.S3x2.isN_set (x : Matrix (Idx r k) (Idx r k) A) :
    IsN x ↔ ∃ g ∈ UcG A (cI r k), (g : Matrix (Idx r k) (Idx r k) A) = x := by sorry
