-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_AAx_congr
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.AAx_congr
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:07:14.099062+00:00
-- url     : https://prove2.me/theorems/6100a3ff-de78-45bc-a32b-aed21dcdb8b7
-- title:
--   Sign Antidiagonal: AAx congr
-- statement:
--   The Sign Antidiagonal construction uses the AAx congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AAvCongr.lean#L63-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AAvCongr.lean#L63-L65

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPeelingMinorMemIdeal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AAvCongr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.AAx_congr {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (xi : Fin r → Fin (2 * r + k + 1) → ℂ) {m1 m2 : ℕ} (h : m1 = m2) (h1 : m1 ≤ r) (h2 : m2 ≤ r) (u : ℂ) :
    AAx k r E xi m1 h1 u = AAx k r E xi m2 h2 u := by sorry
