-- Prove2me | Theorems.Thm_AAInvW_lf_col_of_mulVec
-- name    : AAInvW.lf_col_of_mulVec
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:46:00.403877+00:00
-- url     : https://prove2.me/theorems/174f38cf-678a-4ece-b0c6-e5a602decaa5
-- title:
--   AAInv W: lf col of mul Vec
-- statement:
--   The AAInv W construction uses the lf col of mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SubsetUpperHessenberg.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/SubsetUpperHessenberg.lean#L48-L51

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

theorem AAInvW.lf_col_of_mulVec {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} {j : Fin n} {v : Fin n → ℂ}
    (h : M *ᵥ bvec j = v) (t : Fin n) : M t j = v t := by sorry
