-- Prove2me | Theorems.Thm_AAInvW_herm_mul_bvec
-- name    : AAInvW.herm_mul_bvec
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:26:04.765802+00:00
-- url     : https://prove2.me/theorems/238ce951-be76-465d-b754-a83145c5ed9c
-- title:
--   AAInv W: herm mul bvec
-- statement:
--   The AAInv W construction uses the herm mul bvec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OfFnProdIntertwine.lean#L39-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/OfFnProdIntertwine.lean#L39-L51

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OpModel
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_DetTransposeApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdjointInverseTranslate_OfFnProdIntertwine
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

theorem AAInvW.herm_mul_bvec {N : ℕ} (H g s : Matrix (Fin N) (Fin N) ℂ) (c : Fin N) (w : Fin N → ℂ) :
    herm H ((g * s) *ᵥ bvec c) w = ∑ d, s d c * herm H (g *ᵥ bvec d) w := by sorry
