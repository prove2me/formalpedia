-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HU_aut_cmb
-- name    : Formalism.HermitianLattices.Ext.L3.HU.aut_cmb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:45.926278+00:00
-- url     : https://prove2.me/theorems/b0058769-5858-49d5-bdab-b7284c924a9b
-- title:
--   HU: aut cmb
-- statement:
--   The HU construction uses the aut cmb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomLiftBasis.lean#L237-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsIsomLiftBasis.lean#L237-L253

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CoeCmbSingle
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLiftBasis
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

theorem Formalism.HermitianLattices.Ext.L3.HU.aut_cmb {𝔭 : Ideal (𝓞 F)} (b : Basis κ K V) {g : V ≃ₗ[K] V} {Y : Matrix κ κ (𝓞 K)} {j : ℕ}
    (hgY : ∀ i, g (b i) - ∑ l, Y l i • b l ∈ (extP K 𝔭 ^ j • locF 𝔭 (spanO b) : Submodule (𝓞 K) V))
    (c : κ → 𝓞 K) :
    g (cmb b c : V) - (cmb b (Y *ᵥ c) : V) ∈ (extP K 𝔭 ^ j • locF 𝔭 (spanO b) : Submodule (𝓞 K) V) := by sorry
