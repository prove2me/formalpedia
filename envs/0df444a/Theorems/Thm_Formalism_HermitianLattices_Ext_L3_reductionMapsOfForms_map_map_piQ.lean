-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_reductionMapsOfForms_map_map_piQ
-- name    : Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms.map_map_piQ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:36.622098+00:00
-- url     : https://prove2.me/theorems/4d309735-8c8b-47e7-9d8e-36823e118405
-- title:
--   reduction Maps Of Forms: map map pi Q
-- statement:
--   The reduction Maps Of Forms construction uses the map map pi Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensityEighth.lean#L38-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LocalDensityEighth.lean#L38-L39

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

theorem Formalism.HermitianLattices.Ext.L3.reductionMapsOfForms.map_map_piQ {a b : Type} (𝔭 : Ideal (𝓞 F)) (k : ℕ) (X : Matrix a b (𝓞 K)) :
    (X.map (mkk K 𝔭 (k + 1))).map (piQ K 𝔭 k) = X.map (mkk K 𝔭 k) := by sorry
