-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_W_isDet_mul
-- name    : Formalism.FourierDecayAlt.P.W.isDet_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:35.777802+00:00
-- url     : https://prove2.me/theorems/9911c2c9-c3f7-43fd-aa7a-bba0722486ff
-- title:
--   W: is Det mul
-- statement:
--   The W construction uses the is Det mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstEmbeddingOne.lean#L90-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstEmbeddingOne.lean#L90-L103

import Definitions.Def_Formalism_HermitianCurvature_StatementW
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.W
open Matrix Formalism.YangianSpanCharacter.T NumberField Formalism.FourierDecayAlt.W
variable {R B : Type} [CommRing R] [Ring B] [Algebra R B]

theorem Formalism.FourierDecayAlt.P.W.isDet_mul (M N : R → Matrix (Fin 2) (Fin 2) B) (q qN : R → R) (hM : IsDet M q)
    (hN : IsDet N qN) (hc : EntriesCommute M N) :
    IsDet (fun Y => M Y * N Y) (fun Y => q Y * qN Y) := by sorry
