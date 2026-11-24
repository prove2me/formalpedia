-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_gn_gram_ff
-- name    : Formalism.QuantumDeterminants.gn_gram_ff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:18:55.425726+00:00
-- url     : https://prove2.me/theorems/53341be7-1b66-44eb-8d47-731fb98e79f5
-- title:
--   Quantum Determinants: gn gram ff
-- statement:
--   The Quantum Determinants construction uses the gn gram ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L184-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/GNonneg.lean#L184-L209

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants

theorem Formalism.QuantumDeterminants.gn_gram_ff (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hz : inWb k r z) (a b : Fin (r + 1)) :
    gramM k r z z' g (Sum.inl a) (Sum.inl b) =
      if a.val = r ∧ b.val = r then herm (Hpk k r) z z else 0 := by sorry
