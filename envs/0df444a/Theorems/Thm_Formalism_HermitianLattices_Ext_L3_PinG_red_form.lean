-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinG_red_form
-- name    : Formalism.HermitianLattices.Ext.L3.PinG.red_form
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:38.376703+00:00
-- url     : https://prove2.me/theorems/05cd4a61-3df7-4468-b352-2de534a0c1ae
-- title:
--   Pin G: red form
-- statement:
--   The Pin G construction uses the red form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RedEqOfSubMem.lean#L72-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RedEqOfSubMem.lean#L72-L93

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RedEqOfSubMem
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.PinG
open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable [Fact (IsFixF K F)]

theorem Formalism.HermitianLattices.Ext.L3.PinG.red_form (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, algebraMap (𝓞 K) K (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (k : ℕ) (w w' : ↥(locF 𝔭 (spanO b))) {z : 𝓞 K} (hz : h (w : V) (w' : V) = algebraMap (𝓞 K) K z) :
    star (red b h𝔭 k w) ⬝ᵥ (H.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) *ᵥ red b h𝔭 k w') =
      Ideal.Quotient.mk (extP K 𝔭 ^ k) z := by sorry
