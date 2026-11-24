-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_ioLeft_foldr_left
-- name    : Formalism.QuantumDeterminants.ioLeft_foldr_left
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:48:02.880821+00:00
-- url     : https://prove2.me/theorems/41733af7-2411-49d5-9d15-c84a6da41789
-- title:
--   Quantum Determinants: io Left foldr left
-- statement:
--   The Quantum Determinants construction uses the io Left foldr left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/IOLeft.lean#L30-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/IOLeft.lean#L30-L41

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.REAL
noncomputable section
open Formalism Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.QuantumDeterminants.ioLeft_foldr_left {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (h : Matrix (Fin n) (Fin n) ℂ)
    (L : List ((Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)))
    (hL : ∀ T ∈ L, ∀ f : Matrix (Fin n) (Fin n) ℂ → E, T (fun x => f (h * x)) = fun x => T f (h * x))
    (f : Matrix (Fin n) (Fin n) ℂ → E) :
    L.foldr (fun T g => T g) (fun x => f (h * x)) = fun x => L.foldr (fun T g => T g) f (h * x) := by sorry
