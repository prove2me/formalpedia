-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_row_lo
-- name    : Formalism.QuantumDeterminants.BruhatBigCell.row_lo
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:19:04.88082+00:00
-- url     : https://prove2.me/theorems/273ce318-b188-4c18-a6ce-d6e0a820682f
-- title:
--   Bruhat Big Cell: row lo
-- statement:
--   The Bruhat Big Cell construction uses the row lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BFCell.lean#L60-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BFCell.lean#L60-L72

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

theorem Formalism.QuantumDeterminants.BruhatBigCell.row_lo (p j : Fin (2 * r + k + 1)) (a : Fin r) (hp : p.val = a.val) :
    bigCell k r c μ p j = if j.val = 2 * r + k - a.val then (star (c a))⁻¹ else 0 := by sorry
