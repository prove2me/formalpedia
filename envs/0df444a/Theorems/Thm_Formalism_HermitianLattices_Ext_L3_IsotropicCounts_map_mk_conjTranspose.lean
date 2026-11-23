-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IsotropicCounts_map_mk_conjTranspose
-- name    : Formalism.HermitianLattices.Ext.L3.IsotropicCounts.map_mk_conjTranspose
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:13:18.096561+00:00
-- url     : https://prove2.me/theorems/dd2bed8b-a849-4824-8b35-97e33bf11f3f
-- title:
--   Isotropic Counts: map mk conj Transpose
-- statement:
--   The Isotropic Counts construction uses the map mk conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MapMkConjTranspose.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MapMkConjTranspose.lean#L22-L26

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotExtPPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftUnimod
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardMapEquiv
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardUnitaryFin
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountSplitOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MapMkConjTranspose
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.IsotropicCounts
open Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [hFF : Fact (IsFixF K F)] {m : ℕ}

theorem Formalism.HermitianLattices.Ext.L3.IsotropicCounts.map_mk_conjTranspose (𝔭 : Ideal (𝓞 F)) (k : ℕ) (g : Matrix (Fin m) (Fin m) (𝓞 K)) :
    (g.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)))ᴴ = gᴴ.map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) := by sorry
