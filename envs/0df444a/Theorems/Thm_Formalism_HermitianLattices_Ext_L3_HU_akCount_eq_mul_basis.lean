-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_akCount_eq_mul_basis
-- name    : Formalism.HermitianLattices.Ext.L3.HU.akCount_eq_mul_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:46.077+00:00
-- url     : https://prove2.me/theorems/19abe640-5aa5-463c-be01-1b5b942fe2f0
-- title:
--   HU: ak Count eq mul basis
-- statement:
--   The HU construction uses the ak Count eq mul basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjTransposeEqOfSymm.lean#L93-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjTransposeEqOfSymm.lean#L93-L101

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeMapMk
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryReduction
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjTransposeEqOfSymm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

theorem Formalism.HermitianLattices.Ext.L3.HU.akCount_eq_mul_basis [hFF : Fact (IsFixF K F)] (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V)
    {H : Matrix κ κ (𝓞 K)} (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {c j : ℕ} (he : IsE h (locF 𝔭 (spanO b)) 𝔭 c) (hcj : c ≤ j) (hj : 1 ≤ j) :
    akCount h (locF 𝔭 (spanO b)) 𝔭 (j + c) =
      redCount h (locF 𝔭 (spanO b)) 𝔭 j * sigmaCount h (locF 𝔭 (spanO b)) 𝔭 c := by sorry
