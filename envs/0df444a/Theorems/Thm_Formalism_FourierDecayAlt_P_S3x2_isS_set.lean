-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_isS_set
-- name    : Formalism.FourierDecayAlt.P.S3x2.isS_set
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:23:05.67829+00:00
-- url     : https://prove2.me/theorems/a06aad54-d7ef-4c6b-9083-a6cc064e14a4
-- title:
--   S3x2: is S set
-- statement:
--   The S3x2 construction uses the is S set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L302-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L302-L310

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

theorem Formalism.FourierDecayAlt.P.S3x2.isS_set (x : Matrix (Idx r k) (Idx r k) A) :
    IsS x ↔ ∃ g ∈ PG r (⊤ : Subgroup (GL (Fin k) A)), (g : Matrix (Idx r k) (Idx r k) A) = x := by sorry
