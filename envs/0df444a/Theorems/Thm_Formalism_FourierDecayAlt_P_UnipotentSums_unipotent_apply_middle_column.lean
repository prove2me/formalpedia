-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentSums_unipotent_apply_middle_column
-- name    : Formalism.FourierDecayAlt.P.UnipotentSums.unipotent_apply_middle_column
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:04:47.447516+00:00
-- url     : https://prove2.me/theorems/73836897-de67-4b5d-8c31-8a08b7eb15f5
-- title:
--   Unipotent Sums: unipotent apply middle column
-- statement:
--   The Unipotent Sums construction uses the unipotent apply middle column property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentSums.lean#L100-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentSums.lean#L100-L108

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

theorem Formalism.FourierDecayAlt.P.UnipotentSums.unipotent_apply_middle_column (vX : Matrix (Fin r) (Fin r) ℂ) (p j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val) (hj2 : j.val ≤ r + k) :
    C2.mX k r vX p j = if p = j then 1 else 0 := by sorry
