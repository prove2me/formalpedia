-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_conjO_mem_conjIdeal
-- name    : Formalism.HermitianLattices.Ext.L3.BallB.conjO_mem_conjIdeal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:44:48.182261+00:00
-- url     : https://prove2.me/theorems/c96cc78e-8ec0-4c6b-8db9-96ee9a60d4c5
-- title:
--   Ball B: conj O mem conj Ideal
-- statement:
--   The Ball B construction uses the conj O mem conj Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjOMemConjIdeal.lean#L91-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjOMemConjIdeal.lean#L91-L94

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

theorem Formalism.HermitianLattices.Ext.L3.BallB.conjO_mem_conjIdeal {P : Ideal (𝓞 K)} {π : 𝓞 K} (hπ : π ∈ P) :
    conjO K π ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := K) P := by sorry
