-- Prove2me | Theorems.Thm_AAInvW_lx_mulVec_bvec
-- name    : AAInvW.lx_mulVec_bvec
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:05:15.212713+00:00
-- url     : https://prove2.me/theorems/8990e52c-f904-457e-bf61-0d681eca55aa
-- title:
--   AAInv W: lx mul Vec bvec
-- statement:
--   The AAInv W construction uses the lx mul Vec bvec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/CoefLeftAaVector.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/CoefLeftAaVector.lean#L20-L21

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_SubsetUpperHessenberg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_CoefLeftAaVector
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

theorem AAInvW.lx_mulVec_bvec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (j i : Fin n) : (M *ᵥ bvec j) i = M i j := by sorry
