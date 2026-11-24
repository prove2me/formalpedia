-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_sum_single
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.sum_single
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:05:06.870146+00:00
-- url     : https://prove2.me/theorems/7bd0498d-f4e7-46cc-a8fd-8bb278d20aa5
-- title:
--   Sign Antidiagonal: sum single
-- statement:
--   The Sign Antidiagonal construction uses the sum single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AAvCongr.lean#L30-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AAvCongr.lean#L30-L45

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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.sum_single {M : Type*} [AddCommGroup M] [Module ℂ M] {m N : ℕ} (P : (Fin m → Fin N) → Prop)
    [DecidablePred P] (X : Fin m → Fin N → ℂ) (S : Set (Fin N)) (hX : ∀ a p, p ∉ S → X a p = 0)
    (e : Fin m → Fin N) (he : P e) (huniq : ∀ c, P c → (∀ l, c l ∈ S) → c = e) (F : (Fin m → Fin N) → M) :
    (∑ c : Fin m → Fin N, if P c then (Matrix.of fun a l => X a (c l)).det • F c else 0) =
      (Matrix.of fun a l => X a (e l)).det • F e := by sorry
