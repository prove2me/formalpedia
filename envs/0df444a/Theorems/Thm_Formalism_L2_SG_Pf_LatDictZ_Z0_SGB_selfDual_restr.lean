-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_SGB_selfDual_restr
-- name    : Formalism.L2.SG.Pf.LatDictZ.Z0.SGB.selfDual_restr
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:18:11.265425+00:00
-- url     : https://prove2.me/theorems/b2940db8-9517-470a-bc70-d6252b44d59a
-- title:
--   SGB: self Dual restr
-- statement:
--   The SGB construction uses the self Dual restr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/SelfDualRestr.lean#L123-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SelfDualUnimodular/LocalLatticeDictionary/SelfDualRestr.lean#L123-L145

import Mathlib
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_ExistsUnitNorm
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_SelfDualRestr
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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.SGB
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA Formalism.L2.SG.Pf.LatDictZ.Z0.SGA
variable {K : Type} [Field K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V]
variable {S : Subring K}

theorem Formalism.L2.SG.Pf.LatDictZ.Z0.SGB.selfDual_restr {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : ∀ u v, star (h u v) = h v u) {M : AddSubgroup V}
    (hM : IsSelfDualMod S h M) {X : V} (hXM : X ∈ M) (hXu : IsUnitIn S (h X X)) :
    IsSelfDualMod S (restr h (LinearMap.ker (h X)))
      (M.comap ((LinearMap.ker (h X)).subtype : LinearMap.ker (h X) →ₗ[K] V).toAddMonoidHom) := by sorry
