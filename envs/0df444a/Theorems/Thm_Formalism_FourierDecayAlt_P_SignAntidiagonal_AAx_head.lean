-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_AAx_head
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.AAx_head
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:54:32.266207+00:00
-- url     : https://prove2.me/theorems/cececea0-5b92-4599-adc2-1793b0b36496
-- title:
--   Sign Antidiagonal: AAx head
-- statement:
--   The Sign Antidiagonal construction uses the AAx head property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AAvCongr.lean#L82-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AAvCongr.lean#L82-L99

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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.AAx_head {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (xi : Fin r → Fin (2 * r + k + 1) → ℂ) (i0 : ℕ) (hi0 : i0 ≤ r) (h : Matrix (Fin i0) (Fin i0) ℂ) (u : ℂ)
    (hz : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < i0 → i0 ≤ p.val → xi a p = 0)
    (hh : ∀ a b : Fin i0, xi (Fin.castLE hi0 a) (xR k r i0 hi0 b) = h a b) :
    AAx k r E xi i0 hi0 u = h.det • qminor E (xR k r i0 hi0) (xR k r i0 hi0) u := by sorry
