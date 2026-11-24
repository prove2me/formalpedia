-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatEx_latSpanV_succ
-- name    : Formalism.L2.SG.Pf.LatEx.latSpanV_succ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:12.278411+00:00
-- url     : https://prove2.me/theorems/346f5aa1-d48b-4425-9667-8c7a5a750bf8
-- title:
--   Lat Ex: lat Span V succ
-- statement:
--   The Lat Ex construction uses the lat Span V succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/LatExistsSat.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/LatExistsSat.lean#L23-L29

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

theorem Formalism.L2.SG.Pf.LatEx.latSpanV_succ {n : ℕ} (c : Fin (n + 1) → 𝓕) (v : Fin (n + 1) → V) :
    latSpanV c v = latSpanV (Fin.init c) (Fin.init v) ⊔ lineV (c (Fin.last n)) (v (Fin.last n)) := by sorry
