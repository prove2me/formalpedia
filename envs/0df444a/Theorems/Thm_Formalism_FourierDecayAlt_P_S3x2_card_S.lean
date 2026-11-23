-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_S3x2_card_S
-- name    : Formalism.FourierDecayAlt.P.S3x2.card_S
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:06.003651+00:00
-- url     : https://prove2.me/theorems/0cd7d365-01dd-477c-9fdf-779cb80afcd7
-- title:
--   S3x2: card S
-- statement:
--   The S3x2 construction uses the card S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L345-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReductionSurjective.lean#L345-L347

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

theorem Formalism.FourierDecayAlt.P.S3x2.card_S : Nat.card {x : Matrix (Idx r k) (Idx r k) A // IsS x} =
    Nat.card (PG r (⊤ : Subgroup (GL (Fin k) A))) := by sorry
