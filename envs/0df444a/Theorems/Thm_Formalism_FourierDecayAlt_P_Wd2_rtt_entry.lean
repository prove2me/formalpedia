-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd2_rtt_entry
-- name    : Formalism.FourierDecayAlt.P.Wd2.rtt_entry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:09.551895+00:00
-- url     : https://prove2.me/theorems/099172be-500f-46dc-b3ac-639080c02c12
-- title:
--   Wd2: rtt entry
-- statement:
--   The Wd2 construction uses the rtt entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KroneckerEmbedMulApply.lean#L69-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KroneckerEmbedMulApply.lean#L69-L78

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd2
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K B : Type} [CommRing K] [Ring B] [Algebra K B]

theorem Formalism.FourierDecayAlt.P.Wd2.rtt_entry (M N : Matrix (Fin 2) (Fin 2) B) (D : K)
    (H : (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B) * E1 M * E2 N =
      E2 N * E1 M * (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B))
    (i j k l : Fin 2) :
    D • (M i j * N k l) - M k j * N i l = D • (N k l * M i j) - N k j * M i l := by sorry
