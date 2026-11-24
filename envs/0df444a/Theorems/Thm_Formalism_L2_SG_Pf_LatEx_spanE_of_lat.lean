-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatEx_spanE_of_lat
-- name    : Formalism.L2.SG.Pf.LatEx.spanE_of_lat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:35.359122+00:00
-- url     : https://prove2.me/theorems/f93c1561-01f2-461d-8195-9f9e69cf3fb9
-- title:
--   Lat Ex: span E of lat
-- statement:
--   The Lat Ex construction uses the span E of lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/LatExistsSat.lean#L263-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/LatExistsSat.lean#L263-L276

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsDefs
import Definitions.Def_Lemmata_MiscLemmasD_Imports
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsSat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatEx
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]
local notation "𝓕" => FractionalIdeal (nonZeroDivisors (𝓞 E)) E

theorem Formalism.L2.SG.Pf.LatEx.spanE_of_lat {ι : Type} (N : Submodule (𝓞 E) V) (g : ι → V) (Y : Submodule E V)
    (hNY : N ≤ Y.restrictScalars (𝓞 E)) (hY : Y ≤ Submodule.span E (Set.range g))
    (hg : ∀ i, ∃ t : E, t ≠ 0 ∧ t • g i ∈ N) : Submodule.span E (N : Set V) = Y := by sorry
