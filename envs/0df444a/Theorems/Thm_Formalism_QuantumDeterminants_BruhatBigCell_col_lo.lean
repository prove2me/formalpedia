-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_col_lo
-- name    : Formalism.QuantumDeterminants.BruhatBigCell.col_lo
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:27:00.410471+00:00
-- url     : https://prove2.me/theorems/86a7f81d-8747-4ebd-a425-666cfaa3a8e2
-- title:
--   Bruhat Big Cell: col lo
-- statement:
--   The Bruhat Big Cell construction uses the col lo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BFCell.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BFCell.lean#L36-L42

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

theorem Formalism.QuantumDeterminants.BruhatBigCell.col_lo (i j : Fin (2 * r + k + 1)) (a : Fin r) (hj : j.val = a.val) :
    bigCell k r c μ i j = if i.val = 2 * r + k - a.val then c a else 0 := by sorry
