-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_cls_out
-- name    : Formalism.DoubleCosetMeasures.P.cls_out
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:48.515159+00:00
-- url     : https://prove2.me/theorems/ea2ee5e0-41db-40ed-8a55-0d7219e44f52
-- title:
--   P: cls out
-- statement:
--   The P construction uses the cls out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/TwoSided.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/TwoSided.lean#L36-L39

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_TwoSided
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P

theorem Formalism.DoubleCosetMeasures.P.cls_out {G₁ G₂ : Type} [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (p : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂)) :
    clsTS K₁ K₂ (p.1.out, p.2.out) = p := by sorry
