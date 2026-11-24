-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_ioh_foldr_rep
-- name    : Formalism.QuantumDeterminants.ioh_foldr_rep
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:58:12.931883+00:00
-- url     : https://prove2.me/theorems/f62df059-3a57-4063-8f3f-d19ca1aa177d
-- title:
--   Quantum Determinants: ioh foldr rep
-- statement:
--   The Quantum Determinants construction uses the ioh foldr rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/CapelliHighestWeightConjugated.lean#L184-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/CapelliHighestWeightConjugated.lean#L184-L194

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

theorem Formalism.QuantumDeterminants.ioh_foldr_rep {Eop : Fin n → Fin n → (Matrix (Fin n) (Fin n) ℂ → E) → (Matrix (Fin n) (Fin n) ℂ → E)}
    {Ealg : Fin n → Fin n → Module.End ℂ (ioS ε E)} (hR : IOHRepr Eop Ealg)
    (l : List (ℂ × Fin n × Fin n)) {F : Matrix (Fin n) (Fin n) ℂ → E}
    {x : ioS ε E} (h : IORep F x.1) :
    IORep ((l.map fun p => Top Eop p.1 p.2.1 p.2.2).foldr (fun T f => T f) F)
      ((l.map fun p => Tm Ealg p.1 p.2.1 p.2.2).prod x).1 := by sorry
