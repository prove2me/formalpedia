-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentSums_mX_col_X
-- name    : Formalism.FourierDecayAlt.P.UnipotentSums.mX_col_X
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:04:44.1428+00:00
-- url     : https://prove2.me/theorems/67052888-5ca6-4384-b9d3-71858401dfba
-- title:
--   Unipotent Sums: m X col X
-- statement:
--   The Unipotent Sums construction uses the m X col X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentSums.lean#L84-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentSums.lean#L84-L98

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

theorem Formalism.FourierDecayAlt.P.UnipotentSums.mX_col_X (vX : Matrix (Fin r) (Fin r) ℂ) (p : Fin (2 * r + k + 1)) (c : Fin r) :
    C2.mX k r vX p (eI k r c) = if hp : p.val < r then vX ⟨p.val, hp⟩ c else 0 := by sorry
