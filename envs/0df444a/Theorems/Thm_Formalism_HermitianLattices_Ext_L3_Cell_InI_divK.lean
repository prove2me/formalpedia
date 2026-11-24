-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_InI_divK
-- name    : Formalism.HermitianLattices.Ext.L3.Cell.InI.divK
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T09:46:01.41788+00:00
-- url     : https://prove2.me/theorems/0db8f821-5bae-4b9a-a0ed-aea2e923f2fc
-- title:
--   In I: div K
-- statement:
--   The In I construction uses the div K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CongrPIffInI.lean#L49-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CongrPIffInI.lean#L49-L69

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_InLZeroIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocalData
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CongrPIffInI
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.Cell
open LocalSpans idealPowerSpanBounds localizedQuotients WCA
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K
variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}

theorem Formalism.HermitianLattices.Ext.L3.Cell.InI.divK (h𝔭 : 𝔭.IsMaximal) (hF : IsFixF K F) {D : K} (hD : star D = D) (h0 : InI 𝔭 0 D)
    {v : ℕ} (hv : ¬ InI 𝔭 (v + 1) D) {k : ℕ} {a : K} (ha : InI 𝔭 (v + k) a) :
    InI 𝔭 k (D⁻¹ * a) := by sorry
