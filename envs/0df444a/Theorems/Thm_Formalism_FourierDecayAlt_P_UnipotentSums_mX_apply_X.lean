-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentSums_mX_apply_X
-- name    : Formalism.FourierDecayAlt.P.UnipotentSums.mX_apply_X
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:06:05.852772+00:00
-- url     : https://prove2.me/theorems/0efe4d56-3bc8-467c-b726-f4280c955715
-- title:
--   Unipotent Sums: m X apply X
-- statement:
--   The Unipotent Sums construction uses the m X apply X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentSums.lean#L59-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentSums.lean#L59-L63

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianXiVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CardInsertEmbedding
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.UnipotentSums
open C2x5 C2x6 FlagSpanVanishing HermitianXiVector
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.UnipotentSums.mX_apply_X (vX : Matrix (Fin r) (Fin r) ℂ) (c : Fin r) (j : Fin (2 * r + k + 1)) :
    C2.mX k r vX (eI k r c) j = if hj : j.val < r then vX c ⟨j.val, hj⟩ else 0 := by sorry
