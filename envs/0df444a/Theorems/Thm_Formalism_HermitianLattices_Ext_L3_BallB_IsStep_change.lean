-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_IsStep_change
-- name    : Formalism.HermitianLattices.Ext.L3.BallB.IsStep.change
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:33:57.891122+00:00
-- url     : https://prove2.me/theorems/25f14297-4c25-48b5-a4e4-4f26d2fd89bd
-- title:
--   Is Step: change
-- statement:
--   The Is Step construction uses the change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjOMemConjIdeal.lean#L54-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjOMemConjIdeal.lean#L54-L78

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapConjO
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemConjIdeal
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
open Formalism.HermitianLattices.Ext.L3.BallB.IsStep
variable {P : Ideal (𝓞 K)} {A B : Submodule (𝓞 K) V} {y : V}
omit [StarRing K] [Module K V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.BallB.IsStep.change (S : IsStep P A B y) (hP : P.IsMaximal) {x₀ : V} (hx : x₀ ∈ B) (hn : x₀ ∉ A) :
    IsStep P A B x₀ := by sorry
