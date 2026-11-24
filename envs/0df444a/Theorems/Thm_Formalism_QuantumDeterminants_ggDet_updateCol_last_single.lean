-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_ggDet_updateCol_last_single
-- name    : Formalism.QuantumDeterminants.ggDet_updateCol_last_single
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:18:34.206848+00:00
-- url     : https://prove2.me/theorems/f2ee4036-d986-4055-af59-08191f09db7f
-- title:
--   Quantum Determinants: gg Det update Col last single
-- statement:
--   The Quantum Determinants construction uses the gg Det update Col last single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/ReverseCauchySchwarzHolds.lean#L24-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/ReverseCauchySchwarzHolds.lean#L24-L37

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.QuantumDeterminants

theorem Formalism.QuantumDeterminants.ggDet_updateCol_last_single (n : ℕ) (Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    (updateCol Z (Fin.last n) (Pi.single (Fin.last n) 1)).det =
      (Z.submatrix Fin.castSucc Fin.castSucc).det := by sorry
