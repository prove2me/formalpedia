-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_row_mid_out
-- name    : Formalism.QuantumDeterminants.BruhatBigCell.row_mid_out
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:19:09.001257+00:00
-- url     : https://prove2.me/theorems/dedc3e05-8d1c-4f40-a110-2f217eb5bc31
-- title:
--   Bruhat Big Cell: row mid out
-- statement:
--   The Bruhat Big Cell construction uses the row mid out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BFCell.lean#L89-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BFCell.lean#L89-L95

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BFCell
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
open Formalism.QuantumDeterminants.BruhatBigCell
open GBasic
variable {k r : ℕ}
variable (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)

theorem Formalism.QuantumDeterminants.BruhatBigCell.row_mid_out (p j : Fin (2 * r + k + 1)) (h1 : r ≤ p.val) (h2 : p.val ≤ r + k)
    (hj : j.val < r ∨ r + k < j.val) : bigCell k r c μ p j = 0 := by sorry
