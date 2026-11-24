-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_U0_exists_isASD_loc
-- name    : Formalism.HermitianLattices.Ext.L3.U0.exists_isASD_loc
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:26.647907+00:00
-- url     : https://prove2.me/theorems/31097fd1-afe8-4e1a-8751-40db6e90986a
-- title:
--   U0: exists is ASD loc
-- statement:
--   The U0 construction uses the exists is ASD loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomLocFOfVdZero.lean#L70-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomLocFOfVdZero.lean#L70-L125

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtIffVd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTransfer
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsASDOfTuple
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsFracOfFixed
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLocFOfVdZero
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
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
open Formalism.HermitianLattices.Ext.L3.U0
open WA

theorem Formalism.HermitianLattices.Ext.L3.U0.exists_isASD_loc {h : V →ₗ⋆[K] V →ₗ[K] K} (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm)
    (hd : ∀ x, h x x = 0 → x = 0) {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L)
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hv : vd h L (P.comap (algebraMap (𝓞 F) (𝓞 K))) = 1) {π : K} (hπ : IsUnif (locRing P) π)
    (h1 : ∀ z ∈ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))),
      Dv (locRing P) π (algebraMap (𝓞 K) K z))
    (h2 : ∀ z : 𝓞 K, Dv (locRing P) π (algebraMap (𝓞 K) K z * π⁻¹) →
      z ∈ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ^ 2) :
    ∃ z, IsASD (locRing P) π h ⊤ (Formalism.HermitianLatticesTheory.loc (K := K) P L).toAddSubgroup z := by sorry
