-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormRankFour_herm_e_left
-- name    : Formalism.FourierDecayAlt.P.HermitianFormRankFour.herm_e_left
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:07:31.362802+00:00
-- url     : https://prove2.me/theorems/1be2a381-d5ad-5d54-9555-626211056563
-- title:
--   Hermitian Form Rank Four: herm e left
-- statement:
--   The Hermitian Form Rank Four construction uses the herm e left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L202-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormRankFour.lean#L202-L205

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormRankFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD
open Formalism.FourierDecayAlt.P.HermitianFormRankFour
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.HermitianFormRankFour.herm_e_left (w : Fin (2 * r + k + 1) → ℂ) (c : Fin r) :
    herm (Hpk k r) (bvec (eI k r c)) w = star (w (esI k r c)) := by sorry
