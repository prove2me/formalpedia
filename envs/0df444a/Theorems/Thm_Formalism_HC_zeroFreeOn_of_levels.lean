-- Prove2me | Theorems.Thm_Formalism_HC_zeroFreeOn_of_levels
-- name    : Formalism.HC.zeroFreeOn_of_levels
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:55:25.990232+00:00
-- url     : https://prove2.me/theorems/9c0e7189-a63a-473b-841d-f5e8be837ed8
-- title:
--   HC: zero Free On of levels
-- statement:
--   The HC construction uses the zero Free On of levels property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean#L45-L48

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_Analytic
import Definitions.Def_Formalism_StatementOC
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC

theorem Formalism.HC.zeroFreeOn_of_levels {Q : PChar → Prop} (h : ∀ ψ, Q ψ → ∃ Λ : Level, ψ ∈ Λ.KEPT ∧ Λ.ZeroFreeLevel) : ZeroFreeOn Q := by sorry
