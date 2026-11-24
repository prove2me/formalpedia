-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatEx_peel
-- name    : Formalism.L2.SG.Pf.LatEx.peel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:47.079024+00:00
-- url     : https://prove2.me/theorems/4325ea50-3e90-496f-8151-8268413cb9e0
-- title:
--   Lat Ex: peel
-- statement:
--   The Lat Ex construction uses the peel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/LatExistsSat.lean#L69-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/HaarTransversals/UnitaryHaarProducts/LatExistsSat.lean#L69-L120

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

theorem Formalism.L2.SG.Pf.LatEx.peel {n : ℕ} (w : Fin (n + 1) → V) (hw : LinearIndependent E w) (M : Submodule (𝓞 E) V)
    (hM : M.FG) (hMX : M ≤ (Submodule.span E (Set.range w)).restrictScalars (𝓞 E))
    {d : 𝓞 E} (hd : d ≠ 0) (hdw : d • w (Fin.last n) ∈ M) :
    ∃ (b : 𝓕) (u : V), b ≠ 0 ∧
      M = M ⊓ (Submodule.span E (Set.range (Fin.init w))).restrictScalars (𝓞 E) ⊔ lineV b u := by sorry
