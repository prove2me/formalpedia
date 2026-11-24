-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_absNorm_discrIdeal_of_le
-- name    : Formalism.HermitianLattices.Ext.L3.BallB.absNorm_discrIdeal_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:57.014797+00:00
-- url     : https://prove2.me/theorems/416098bb-076c-4af9-bb33-911b6abdd6b2
-- title:
--   Ball B: abs Norm discr Ideal of le
-- statement:
--   The Ball B construction uses the abs Norm discr Ideal of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AbsNormDiscrIdealOfLe.lean#L168-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AbsNormDiscrIdealOfLe.lean#L168-L241

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemConjIdeal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormDiscrIdealOfLe
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BallB
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.BallB.absNorm_discrIdeal_of_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    {B : Submodule (𝓞 K) V} (hB : Formalism.HermitianLatticesTheory.IsIntegralLat h B)
    (b : Basis (Fin (finrank K V)) K V) :
    ∀ (n : ℕ) (A : Submodule (𝓞 K) V), A ≤ B → A.toAddSubgroup.relIndex B.toAddSubgroup = n →
      n ≠ 0 → Ideal.absNorm (discrIdeal h A) = n ^ 2 * Ideal.absNorm (discrIdeal h B) := by sorry
