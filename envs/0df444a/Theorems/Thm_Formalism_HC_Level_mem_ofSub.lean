-- Prove2me | Theorems.Thm_Formalism_HC_Level_mem_ofSub
-- name    : Formalism.HC.Level.mem_ofSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:35.002096+00:00
-- url     : https://prove2.me/theorems/36e919a3-1860-4836-bdd5-381007979d20
-- title:
--   Level: mem of Sub
-- statement:
--   The Level construction uses the mem of Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean#L116-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean#L116-L119

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

theorem Formalism.HC.Level.mem_ofSub {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (ψ : PChar) :
    ψ ∈ (Level.ofSub Ξ).KEPT ↔ ∃ χ ∈ Ξ, PChar.of χ = ψ := by sorry
