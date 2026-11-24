-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinG_red_gM
-- name    : Formalism.HermitianLattices.Ext.L3.PinG.red_gM
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:58:09.305318+00:00
-- url     : https://prove2.me/theorems/7dac1893-28fc-4d8c-8065-4f47d08de46a
-- title:
--   Pin G: red g M
-- statement:
--   The Pin G construction uses the red g M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RedEqOfSubMem.lean#L112-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RedEqOfSubMem.lean#L112-L131

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
omit [Fact (IsFixF K F)]

theorem Formalism.HermitianLattices.Ext.L3.PinG.red_gM {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    [𝔭.IsPrime] (k : ℕ) {g : V ≃ₗ[K] V} (hg : g ∈ autSub h (locF 𝔭 (spanO b)))
    (w : ↥(locF 𝔭 (spanO b))) : red b h𝔭 k (gM hg w) = gMat b h𝔭 k hg *ᵥ red b h𝔭 k w := by sorry
