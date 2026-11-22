-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_mem_PG
-- name    : Formalism.FourierDecayAlt.P.S3x2.mem_PG
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:21:35.815353+00:00
-- url     : https://prove2.me/theorems/0921de29-f77e-48f1-9bff-9c1a63da79cf
-- title:
--   S3x2: mem PG
-- statement:
--   The S3x2 construction uses the mem PG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L282-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L282-L289

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

theorem Formalism.FourierDecayAlt.P.S3x2.mem_PG (V : Subgroup (GL (Fin k) A)) (g : GL (Idx r k) A) :
    g ∈ PG r V ↔ ∃ n : GL (Idx r k) A, ∃ h ∈ V, IsN (n : Matrix (Idx r k) (Idx r k) A) ∧
      g = n * phi A r k h := by sorry
