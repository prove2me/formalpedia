-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_not_le_of_vd_eq_zero
-- name    : Formalism.HermitianLattices.Ext.L3.LocF.not_le_of_vd_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:54:08.401007+00:00
-- url     : https://prove2.me/theorems/867b589b-5ba5-4ff7-b061-a9f7dc95ab37
-- title:
--   Loc F: not le of vd eq zero
-- statement:
--   The Loc F construction uses the not le of vd eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/VdEqZeroOfNotLe.lean#L65-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/VdEqZeroOfNotLe.lean#L65-L78

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapIntCastSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LinearIndependentOfGramDetNeZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_VdEqZeroOfNotLe
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.LocF.not_le_of_vd_eq_zero {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
    (hD : discrIdeal h L ≠ ⊥) (hE : extP K 𝔭 ≠ ⊤) (h0 : vd h L 𝔭 = 0) :
    ¬ discrIdeal h L ≤ extP K 𝔭 := by sorry
