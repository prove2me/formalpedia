-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_strictMono_snoc
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.strictMono_snoc
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:14:00.971799+00:00
-- url     : https://prove2.me/theorems/8604ef3c-976b-4015-a336-47dfdc2c5f07
-- title:
--   Sign Antidiagonal: strict Mono snoc
-- statement:
--   The Sign Antidiagonal construction uses the strict Mono snoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StrictMonoSnoc.lean#L59-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StrictMonoSnoc.lean#L59-L74

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondExpansionIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StrictMonoSnoc
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

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.strictMono_snoc {α : Type} [Preorder α] {m : ℕ} (f : Fin m → α) (hf : StrictMono f) (x : α)
    (hx : ∀ l, f l < x) : StrictMono (Fin.snoc (α := fun _ => α) f x : Fin (m + 1) → α) := by sorry
