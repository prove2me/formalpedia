-- Prove2me | Theorems.Thm_Formalism_HC_Level_mem_cyc
-- name    : Formalism.HC.Level.mem_cyc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:44.714736+00:00
-- url     : https://prove2.me/theorems/433a4183-04f2-45d8-8060-9efdbde5131c
-- title:
--   Level: mem cyc
-- statement:
--   The Level construction uses the mem cyc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean#L123-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean#L123-L124

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

theorem Formalism.HC.Level.mem_cyc (ψ : PChar) : ψ ∈ (Level.cyc ψ).KEPT := by sorry
