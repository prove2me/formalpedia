-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BallB_term_mem
-- name    : Formalism.HermitianLattices.Ext.L3.BallB.term_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:45:12.072688+00:00
-- url     : https://prove2.me/theorems/1988b376-0fa3-4b1d-8b51-886d2b895b2f
-- title:
--   Ball B: term mem
-- statement:
--   The Ball B construction uses the term mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjOMemConjIdeal.lean#L96-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjOMemConjIdeal.lean#L96-L99

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

theorem Formalism.HermitianLattices.Ext.L3.BallB.term_mem {P I : Ideal (𝓞 K)} {p₁ p₂ z : 𝓞 K} (h₁ : p₁ ∈ P) (h₂ : p₂ ∈ P) (hz : z ∈ I) :
    conjO K p₁ * p₂ * z ∈ P * Formalism.HermitianLatticesTheory.conjIdeal (K := K) P * I := by sorry
