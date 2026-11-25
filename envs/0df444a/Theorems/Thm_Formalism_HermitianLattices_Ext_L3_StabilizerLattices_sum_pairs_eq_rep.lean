-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_StabilizerLattices_sum_pairs_eq_rep
-- name    : Formalism.HermitianLattices.Ext.L3.StabilizerLattices.sum_pairs_eq_rep
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:43:48.460445+00:00
-- url     : https://prove2.me/theorems/7bb6a6ac-954b-425d-8e00-6a9f284d472a
-- title:
--   Stabilizer Lattices: sum pairs eq rep
-- statement:
--   The Stabilizer Lattices construction uses the sum pairs eq rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsClassReps.lean#L63-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsClassReps.lean#L63-L81

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsClassReps
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
open Formalism.HermitianLattices.Ext.L3.StabilizerLattices
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem Formalism.HermitianLattices.Ext.L3.StabilizerLattices.sum_pairs_eq_rep (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V} (n : K)
    {s : Finset (Submodule (𝓞 K) V)} (hsr : Formalism.ThetaLiftIndependence.IsClassReps h L s)
    {sX : Finset (Submodule (𝓞 K) V × V)} (hsX : ∀ t ∈ sX, t ∈ pairs h L n)
    (hX : ∀ p ∈ pairs h L n, ∃! t, t ∈ sX ∧ ∃ g : Formalism.HermitianLatticesTheory.isom h, g • t = p) :
    ∑ t ∈ sX, ((Nat.card (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) t) : ℕ) : ℝ)⁻¹ =
      ∑ M ∈ s, (repCount h M n : ℝ) / ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ) := by sorry
