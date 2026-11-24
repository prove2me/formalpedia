-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_zOnly
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z3.zOnly
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:57:37.907807+00:00
-- url     : https://prove2.me/theorems/2e6209f3-5d3a-4625-bfd1-b27050dea228
-- title:
--   Z3: z Only
-- statement:
--   The Z3 construction uses the z Only property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZZLoc.lean#L412-L544
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZZLoc.lean#L412-L544

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZZLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z3
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem Formalism.L2.SG.Pf.LatDictZ.Z3.zOnly (h1 : SemiGenusLoc) (h2 : PrimPlaneLoc) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm)
    (hd : ∀ x, (∀ y, h x y = 0) → x = 0) {p : Ideal (𝓞 K)} (hp : p.IsMaximal) (z : V)
    (M₁ M₂ : AddSubgroup V) (hM₁ : IsSelfDualMod (locRing p) h M₁)
    (hM₂ : IsSelfDualMod (locRing p) h M₂) (hz₁ : z ∈ M₁) (hz₂ : z ∈ M₂)
    (hp₁ : ∀ c : K, c • z ∈ M₁ → c ∈ locRing p) (hp₂ : ∀ c : K, c • z ∈ M₂ → c ∈ locRing p) :
    ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, g z = z ∧ ∀ x, x ∈ M₁ ↔ g x ∈ M₂ := by sorry
