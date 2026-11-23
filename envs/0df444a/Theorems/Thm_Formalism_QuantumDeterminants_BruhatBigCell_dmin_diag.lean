-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_BruhatBigCell_dmin_diag
-- name    : Formalism.QuantumDeterminants.BruhatBigCell.dmin_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:01:59.79419+00:00
-- url     : https://prove2.me/theorems/af20a787-caca-4e5a-8471-35ae16402d4b
-- title:
--   Bruhat Big Cell: dmin diag
-- statement:
--   The Bruhat Big Cell construction uses the dmin diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BFCell.lean#L226-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/BFCell.lean#L226-L232

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

theorem Formalism.QuantumDeterminants.BruhatBigCell.dmin_diag {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (d : Fin (r + 1) → ℂ)
    (hZ : Zhat k r z z' g = diagonal d) (l : Fin (r + 2)) :
    Dmin k r z z' g l = ∏ i : Fin l.val, d (Fin.castLE (Nat.le_of_lt_succ l.isLt) i) := by sorry
