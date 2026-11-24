-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGA_exists_norm_eq
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z0.SGA.exists_norm_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:57:40.470809+00:00
-- url     : https://prove2.me/theorems/90f05f31-0c83-4533-874b-730caf7c4c39
-- title:
--   SGA: exists norm eq
-- statement:
--   The SGA construction uses the exists norm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/ExistsUnitNorm.lean#L169-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/ExistsUnitNorm.lean#L169-L247

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_ExistsUnitNorm
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V]

theorem Formalism.L2.SG.Pf.LatDictZ.Z0.SGA.exists_norm_eq {p : Ideal (𝓞 K)} (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hp : p.IsMaximal)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : ∀ x, (∀ y, h x y = 0) → x = 0)
    {M : AddSubgroup V} (hM : IsSelfDualMod (locRing p) h M) (e : V)
    (he : IsUnitIn (locRing p) (h e e)) :
    ∃ X ∈ M, h X X = h e e := by sorry
