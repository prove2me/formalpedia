-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z3_exists_dual_one
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z3.exists_dual_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:57:58.632799+00:00
-- url     : https://prove2.me/theorems/1c031f17-6c66-4b96-9990-3fe1549a4a84
-- title:
--   Z3: exists dual one
-- statement:
--   The Z3 construction uses the exists dual one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZZLoc.lean#L365-L410
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/LatDictZZLoc.lean#L365-L410

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

theorem Formalism.L2.SG.Pf.LatDictZ.Z3.exists_dual_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm)
    (hd : ∀ x, (∀ y, h x y = 0) → x = 0) {p : Ideal (𝓞 K)} (hp : p.IsMaximal) {z : V}
    {M₁ : AddSubgroup V} (hM₁ : IsSelfDualMod (locRing p) h M₁) (hz₁ : z ∈ M₁)
    (hp₁ : ∀ c : K, c • z ∈ M₁ → c ∈ locRing p) (hz0 : z ≠ 0) : ∃ y₁ ∈ M₁, h z y₁ = 1 := by sorry
