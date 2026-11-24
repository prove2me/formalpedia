-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatEx_sub_smul_mem_span_init
-- name    : Formalism.L2.SG.Pf.LatEx.sub_smul_mem_span_init
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:18.799963+00:00
-- url     : https://prove2.me/theorems/9bebfc71-7e79-471c-9a38-51698046738e
-- title:
--   Lat Ex: sub smul mem span init
-- statement:
--   The Lat Ex construction uses the sub smul mem span init property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/LatExistsSat.lean#L46-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/LatExistsSat.lean#L46-L56

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

theorem Formalism.L2.SG.Pf.LatEx.sub_smul_mem_span_init {n : ℕ} (w : Fin (n + 1) → V) (f : V →ₗ[E] E)
    (hf1 : f (w (Fin.last n)) = 1) (hf0 : ∀ i : Fin n, f (w i.castSucc) = 0) {x : V}
    (hx : x ∈ Submodule.span E (Set.range w)) :
    x - f x • w (Fin.last n) ∈ Submodule.span E (Set.range (Fin.init w)) := by sorry
