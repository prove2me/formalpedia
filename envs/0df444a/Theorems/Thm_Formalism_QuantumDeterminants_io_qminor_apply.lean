-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_io_qminor_apply
-- name    : Formalism.QuantumDeterminants.io_qminor_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:34:32.021517+00:00
-- url     : https://prove2.me/theorems/3fc39229-2880-4166-9b48-78f0d10e7e50
-- title:
--   Quantum Determinants: io qminor apply
-- statement:
--   The Quantum Determinants construction uses the io qminor apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/IOCentral.lean#L265-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/IOCentral.lean#L265-L270

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
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

theorem Formalism.QuantumDeterminants.io_qminor_apply {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) (x : ioS ε E) :
    qminor (ioE ε E) a b u x = ∑ σ : Equiv.Perm (Fin t), (((Equiv.Perm.sign σ : ℤ) : ℂ)) •
      ((List.ofFn fun k : Fin t => (u - ((k : ℕ) : ℂ), a (σ k), b k)).map
        fun p => Tm (ioE ε E) p.1 p.2.1 p.2.2).prod x := by sorry
