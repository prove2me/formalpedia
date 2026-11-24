-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_nO_gram
-- name    : Formalism.HermitianLattices.Ext.L3.D2.nO_gram
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T09:48:35.148173+00:00
-- url     : https://prove2.me/theorems/ed811015-fd4c-4a66-8399-72bbad55c444
-- title:
--   D2: n O gram
-- statement:
--   The D2 construction uses the n O gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MulMemPrimePower.lean#L178-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MulMemPrimePower.lean#L178-L224

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulEqUnifPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulMemPrimePower
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_Ent_det

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem Formalism.HermitianLattices.Ext.L3.D2.nO_gram (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (a : Basis (Fin (finrank K V)) K V)
    (ha : locF 𝔭 (Submodule.span (𝓞 K) (Set.range a)) = locF 𝔭 A₀) :
    (Matrix.of fun i j => h (a i) (a j)).det ∈ pK K 𝔭 0 ∧
      (Matrix.of fun i j => h (a i) (a j)).det ≠ 0 ∧
      nO 𝔭 (Matrix.of fun i j => h (a i) (a j)).det =
        Ideal.absNorm 𝔭 ^ (2 * vd h (locF 𝔭 A₀) 𝔭) := by sorry
