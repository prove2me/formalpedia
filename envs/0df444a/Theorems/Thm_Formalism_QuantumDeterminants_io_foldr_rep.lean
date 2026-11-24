-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_io_foldr_rep
-- name    : Formalism.QuantumDeterminants.io_foldr_rep
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:34:23.017035+00:00
-- url     : https://prove2.me/theorems/8ecdc3cf-e1a5-455c-9c49-f44e4ead8bc7
-- title:
--   Quantum Determinants: io foldr rep
-- statement:
--   The Quantum Determinants construction uses the io foldr rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/IOCentral.lean#L253-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/IOCentral.lean#L253-L263

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

theorem Formalism.QuantumDeterminants.io_foldr_rep (l : List (ℂ × Fin n × Fin n)) {F : Matrix (Fin n) (Fin n) ℂ → E}
    {x : ioS ε E} (h : IORep F x.1) :
    IORep ((l.map fun p => Top (EabV ε) p.1 p.2.1 p.2.2).foldr (fun T f => T f) F)
      ((l.map fun p => Tm (ioE ε E) p.1 p.2.1 p.2.2).prod x).1 := by sorry
