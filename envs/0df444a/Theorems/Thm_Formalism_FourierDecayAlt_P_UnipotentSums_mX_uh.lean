-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentSums_mX_uh
-- name    : Formalism.FourierDecayAlt.P.UnipotentSums.mX_uh
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:05:43.575638+00:00
-- url     : https://prove2.me/theorems/bed74017-c415-464e-b9da-2e24a672244d
-- title:
--   Unipotent Sums: m X uh
-- statement:
--   The Unipotent Sums construction uses the m X uh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentSums.lean#L135-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentSums.lean#L135-L205

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

theorem Formalism.FourierDecayAlt.P.UnipotentSums.mX_uh (vX : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit vX.det) : C2.mX k r vX ∈ UH (Hpk k r) := by sorry
