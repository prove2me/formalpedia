-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_dcMap_eq_iff
-- name    : Formalism.DoubleCosetMeasures.P.dcMap_eq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:38.806505+00:00
-- url     : https://prove2.me/theorems/d489fdb2-f42a-4534-844f-a3c74b7b813a
-- title:
--   P: dc Map eq iff
-- statement:
--   The P construction uses the dc Map eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/DoubleCosetEqPreimage.lean#L147-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/DoubleCosetEqPreimage.lean#L147-L152

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_DoubleCosetEqPreimage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
variable {G : Type} [Group G]

theorem Formalism.DoubleCosetMeasures.P.dcMap_eq_iff (K₀ : Subgroup G) (g : G) (k k' : K₀) :
    dcMap K₀ g k = dcMap K₀ g k' ↔
      k⁻¹ * k' ∈ (K₀.map (MulAut.conj g).toMonoidHom).subgroupOf K₀ := by sorry
