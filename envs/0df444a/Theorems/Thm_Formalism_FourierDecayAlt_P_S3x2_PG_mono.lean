-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_PG_mono
-- name    : Formalism.FourierDecayAlt.P.S3x2.PG_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:41:56.516682+00:00
-- url     : https://prove2.me/theorems/af7e865c-0995-4adc-a434-31da3cb85a2f
-- title:
--   S3x2: PG mono
-- statement:
--   The S3x2 construction uses the PG mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L337-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L337-L340

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

theorem Formalism.FourierDecayAlt.P.S3x2.PG_mono {V W : Subgroup (GL (Fin k) A)} (h : V ≤ W) : PG r V ≤ PG r W := by sorry
