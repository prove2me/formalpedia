-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Cell_exact_step
-- name    : Formalism.HermitianLattices.Ext.L3.Cell.exact_step
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:28:22.265178+00:00
-- url     : https://prove2.me/theorems/58474c16-036d-50af-9cdb-64fb339c9bd4
-- title:
--   Cell: exact step
-- statement:
--   The Cell construction uses the exact step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNearRepresentation.lean#L23-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNearRepresentation.lean#L23-L49

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CongrPIffInI
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSmulMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNearRepresentation
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

theorem Formalism.HermitianLattices.Ext.L3.Cell.exact_step {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {b x : V}
    (hd : h (x - b) (x - b) ≠ 0) :
    h (b - ((h b (x - b) + h (x - b) b) * (h (x - b) (x - b))⁻¹) • (x - b))
        (b - ((h b (x - b) + h (x - b) b) * (h (x - b) (x - b))⁻¹) • (x - b)) = h b b ∧
      (b - ((h b (x - b) + h (x - b) b) * (h (x - b) (x - b))⁻¹) • (x - b)) - x =
        -(((h (x - b) (x - b))⁻¹ * (h x x - h b b)) • (x - b)) := by sorry
