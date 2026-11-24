-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_third_peeling_minor_mem_ideal
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.third_peeling_minor_mem_ideal
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:33:50.118606+00:00
-- url     : https://prove2.me/theorems/a9c612c6-429e-49fb-9c97-58e03aea73c7
-- title:
--   Sign Antidiagonal: third peeling minor mem ideal
-- statement:
--   The Sign Antidiagonal construction uses the third peeling minor mem ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThirdPeelingMinorMemIdeal.lean#L71-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThirdPeelingMinorMemIdeal.lean#L71-L130

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstPeelingMinorMemIdeal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPeelingMinorMemIdeal
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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.third_peeling_minor_mem_ideal {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (hG : GlRel E) (ell : ℂ) : ∀ (m i : ℕ), i ≤ m → m + 1 ≤ r →
    qminor E (fun l : Fin m => ps k r (if l.val < i then l.val else l.val + 1)) (fun l : Fin m => ps k r l.val)
        (ell + (m : ℂ) - 1) -
      qminor E (fun l : Fin i => ps k r l.val) (fun l : Fin i => ps k r l.val) (ell + (i : ℂ) - 1) ∈
      Ideal.span (rgen k r z' E) := by sorry
