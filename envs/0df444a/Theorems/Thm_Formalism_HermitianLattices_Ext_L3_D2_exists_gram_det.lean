-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_gram_det
-- name    : Formalism.HermitianLattices.Ext.L3.D2.exists_gram_det
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T09:54:53.836336+00:00
-- url     : https://prove2.me/theorems/d0fb020c-e6b0-4297-92cc-7040e0aff2b9
-- title:
--   D2: exists gram det
-- statement:
--   The D2 construction uses the exists gram det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MulMemPrimePower.lean#L40-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MulMemPrimePower.lean#L40-L84

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
open HermitianSublattices LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans traceDeterminantCongruences reductionMapsOfForms localValuationFiltration

theorem Formalism.HermitianLattices.Ext.L3.D2.exists_gram_det (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (b : Basis (Fin (finrank K V)) K V) (hbL : ∀ i, b i ∈ L)
    (hb : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L) :
    ∃ D : 𝓞 F, D ≠ 0 ∧ (Matrix.of fun i j => h (b i) (b j)).det = algebraMap (𝓞 K) K (ι D) ∧
      vd h L 𝔭 = vF 𝔭 D := by sorry
