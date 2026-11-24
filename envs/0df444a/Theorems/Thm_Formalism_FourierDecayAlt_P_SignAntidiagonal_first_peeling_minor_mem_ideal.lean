-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_first_peeling_minor_mem_ideal
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.first_peeling_minor_mem_ideal
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:15:36.950067+00:00
-- url     : https://prove2.me/theorems/bb9ad563-2f56-415f-baf8-d285fb486c24
-- title:
--   Sign Antidiagonal: first peeling minor mem ideal
-- statement:
--   The Sign Antidiagonal construction uses the first peeling minor mem ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstPeelingMinorMemIdeal.lean#L102-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/FirstPeelingMinorMemIdeal.lean#L102-L160

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThirdPolynomialExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstPeelingMinorMemIdeal
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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.first_peeling_minor_mem_ideal {A : Type} [Ring A] [Algebra ℂ A] (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (u : ℂ) : ∀ (m i : ℕ), i ≤ m → m + 1 ≤ r →
    qminor E (fun l : Fin m => pe k r l.val) (fun l : Fin m => pe k r (if l.val < i then l.val else l.val + 1)) u -
      qminor E (fun l : Fin i => pe k r l.val) (fun l : Fin i => pe k r l.val) u ∈ Ideal.span (rgen k r z' E) := by sorry
