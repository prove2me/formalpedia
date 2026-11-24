-- Prove2me | Theorems.Thm_AAInvW_lf_UW_col
-- name    : AAInvW.lf_UW_col
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T15:55:50.246165+00:00
-- url     : https://prove2.me/theorems/9b211c42-2d68-4bf5-b1e5-6d97580ea073
-- title:
--   AAInv W: lf UW col
-- statement:
--   The AAInv W construction uses the lf UW col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SubsetUpperHessenberg.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SubsetUpperHessenberg.lean#L104-L107

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_HkConjTranspose
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open AAInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3

theorem AAInvW.lf_UW_col (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) (a : Fin r) (t : Fin (2 * r + k + 1)) :
    h t (eI k r a) = if t = eI k r a then 1 else 0 := by sorry
