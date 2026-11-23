-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_IsStep_mem_of_smul_mem
-- name    : Formalism.HermitianLattices.Ext.L3.BallB.IsStep.mem_of_smul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:13:18.118841+00:00
-- url     : https://prove2.me/theorems/6b277a0d-0371-49cf-92b3-03bb1f78e8b0
-- title:
--   Is Step: mem of smul mem
-- statement:
--   The Is Step construction uses the mem of smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjOMemConjIdeal.lean#L43-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjOMemConjIdeal.lean#L43-L51

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

theorem Formalism.HermitianLattices.Ext.L3.BallB.IsStep.mem_of_smul_mem (S : IsStep P A B y) (hP : P.IsMaximal) {c : 𝓞 K} (hc : c • y ∈ A) :
    c ∈ P := by sorry
