-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_reductionMapsOfForms_map_form
-- name    : Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms.map_form
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:21.010551+00:00
-- url     : https://prove2.me/theorems/c0da18d0-2a2b-4a55-bfb3-909864c191ed
-- title:
--   reduction Maps Of Forms: map form
-- statement:
--   The reduction Maps Of Forms construction uses the map form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensityEighth.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensityEighth.lean#L33-L36

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySeventh
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEighth
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m r : Type} [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq r]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)

theorem Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms.map_form {a b : Type} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (H : Matrix m m (𝓞 K)) (X : Matrix m a (𝓞 K))
    (Y : Matrix m b (𝓞 K)) :
    (X.map (mkk K 𝔭 k))ᴴ * H.map (mkk K 𝔭 k) * Y.map (mkk K 𝔭 k) = (Xᴴ * H * Y).map (mkk K 𝔭 k) := by sorry
