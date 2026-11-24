-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_ioh_qminor_rep
-- name    : Formalism.QuantumDeterminants.ioh_qminor_rep
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:58:33.005811+00:00
-- url     : https://prove2.me/theorems/beaa783b-8b70-48de-9276-1232d787cab7
-- title:
--   Quantum Determinants: ioh qminor rep
-- statement:
--   The Quantum Determinants construction uses the ioh qminor rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/CapelliHighestWeightConjugated.lean#L207-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/CapelliHighestWeightConjugated.lean#L207-L219

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
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem Formalism.QuantumDeterminants.ioh_qminor_rep {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}
    {Ealg : Fin n → Fin n → Module.End ℂ (ioS ε E)} (hR : IOHRepr Eop Ealg)
    {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) {F : Matrix (Fin n) (Fin n) ℂ → E}
    {x : ioS ε E} (h : IORep F x.1) :
    IORep (qminorOp Eop a b u F) (qminor Ealg a b u x).1 := by sorry
