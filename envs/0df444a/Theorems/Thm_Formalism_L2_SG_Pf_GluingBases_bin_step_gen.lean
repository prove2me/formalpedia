-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_GluingBases_bin_step_gen
-- name    : Formalism.L2.SG.Pf.GluingBases.bin_step_gen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:48.311403+00:00
-- url     : https://prove2.me/theorems/b153802c-c4ff-418f-a9cd-e0a63f1273e0
-- title:
--   Gluing Bases: bin step gen
-- statement:
--   The Gluing Bases construction uses the bin step gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsPrescFamily.lean#L14-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsPrescFamily.lean#L14-L31

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLand
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsPrescFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.GluingBases
open Formalism.HermitianLattices.Ext.L3
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem Formalism.L2.SG.Pf.GluingBases.bin_step_gen (h : V →ₗ⋆[K] V →ₗ[K] K) (hz : ∀ x y, h x y = 0 → h y x = 0) (e₁ e₂ : V)
    (a b x y n : K) (h12 : h e₁ e₂ = 0) (h11 : h e₁ e₁ = a) (h22 : h e₂ e₂ = b) (ha : star a = a)
    (hb : star b = b) (hxy : a * (x * star x) + b * (y * star y) = n) :
    h (x • e₁ + y • e₂) (x • e₁ + y • e₂) = n ∧
      h (x • e₁ + y • e₂) ((star y * b) • e₁ - (star x * a) • e₂) = 0 ∧
      h ((star y * b) • e₁ - (star x * a) • e₂) ((star y * b) • e₁ - (star x * a) • e₂) =
        a * b * n := by sorry
