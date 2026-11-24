-- Prove2me | Theorems.Thm_Formalism_MainNotions_G_Inhab_smul1
-- name    : Formalism.MainNotions.G.Inhab.smul1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:18:00.188857+00:00
-- url     : https://prove2.me/theorems/194098dc-e0d3-407e-8f81-a1277f78b4ed
-- title:
--   Inhab: smul1
-- statement:
--   The Inhab construction uses the smul1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataLoc.lean#L154-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/TensorLatticeBounds/DataLoc.lean#L154-L160

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataGChain
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_GatSetting
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TensorLatticeBounds_DataLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.Inhab
open Formalism.MainNotions.G
variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem Formalism.MainNotions.G.Inhab.smul1 (h : HidaSetting p n' W Qq O Kf ι σ j w) (γ : Multiplicative ℤ) (L : (places1 h).Tup) (n : ℤ)
    (hL : L (0 : Fin 1) = line W p n) :
    (level1 h).smul γ L (0 : Fin 1) = line W p (Multiplicative.toAdd γ + n) := by sorry
