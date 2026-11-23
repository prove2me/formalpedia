-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_card_PG
-- name    : Formalism.FourierDecayAlt.P.S3x2.card_PG
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:09.707127+00:00
-- url     : https://prove2.me/theorems/0dace42d-de06-4853-9a96-8fd0bb2dce60
-- title:
--   S3x2: card PG
-- statement:
--   The S3x2 construction uses the card PG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L278-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L278-L280

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

theorem Formalism.FourierDecayAlt.P.S3x2.card_PG (V : Subgroup (GL (Fin k) A)) :
    Nat.card (PG r V) = Nat.card (UcG A (cI r k)) * Nat.card V := by sorry
