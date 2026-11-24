-- Prove2me | Theorems.Thm_AAInvW_lx_sum_red
-- name    : AAInvW.lx_sum_red
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:04:43.579143+00:00
-- url     : https://prove2.me/theorems/42ce9b5b-069c-4d3d-80e7-a52b04186bd7
-- title:
--   AAInv W: lx sum red
-- statement:
--   The AAInv W construction uses the lx sum red property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/CoefLeftAaVector.lean#L39-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdjointInverseTranslate/CoefLeftAaVector.lean#L39-L47

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

theorem AAInvW.lx_sum_red {n m : ℕ} (e : Fin m → Fin n) (he : Function.Injective e) (F : Fin n → ℂ)
    (hF : ∀ j, j ∉ Set.range e → F j = 0) : ∑ j, F j = ∑ b, F (e b) := by sorry
