-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_hpk_mulVec_apply
-- name    : Formalism.QuantumDeterminants.BruhatBigCell.hpk_mulVec_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:19:06.493797+00:00
-- url     : https://prove2.me/theorems/e1fd0673-f67d-4b5e-b6fd-ea0cd0e019f6
-- title:
--   Bruhat Big Cell: hpk mul Vec apply
-- statement:
--   The Bruhat Big Cell construction uses the hpk mul Vec apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BFCell.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BFCell.lean#L24-L29

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

theorem Formalism.QuantumDeterminants.BruhatBigCell.hpk_mulVec_apply (v : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) p = sgn k r p * v (sig k r p) := by sorry
