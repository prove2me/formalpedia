-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_ioh_qminor
-- name    : Formalism.QuantumDeterminants.ioh_qminor
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:56:28.496509+00:00
-- url     : https://prove2.me/theorems/00020bc7-d860-4f2e-8b5e-939ef696bf87
-- title:
--   Quantum Determinants: ioh qminor
-- statement:
--   The Quantum Determinants construction uses the ioh qminor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/CapelliHighestWeightConjugated.lean#L283-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/CapelliHighestWeightConjugated.lean#L283-L298

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOLeft
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_CapelliHighestWeightConjugated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.QuantumDeterminants.ioh_qminor (ε : Fin n → Bool) (H P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1)
    (hPQ : P * Q = 1) (hH : H = Pᴴ * Jm ε * P) {t : ℕ} (α β : Fin t → Fin n) (u : ℂ)
    (G : Matrix (Fin n) (Fin n) ℂ → E) (x : Matrix (Fin n) (Fin n) ℂ) :
    qminorOp (EabH H) α β u G x =
      qminorOp (fun a b => EcV ε (P * Matrix.single a b 1 * Q)) α β u (fun y => G (Q * y * P))
        (P * x * Q) := by sorry
