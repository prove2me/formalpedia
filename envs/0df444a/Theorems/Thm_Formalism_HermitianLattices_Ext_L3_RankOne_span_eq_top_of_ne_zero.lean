-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_RankOne_span_eq_top_of_ne_zero
-- name    : Formalism.HermitianLattices.Ext.L3.RankOne.span_eq_top_of_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:45:10.588792+00:00
-- url     : https://prove2.me/theorems/20b34ed1-f9e9-42f0-88ad-151e97052adc
-- title:
--   Rank One: span eq top of ne zero
-- statement:
--   The Rank One construction uses the span eq top of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNeZeroOfIsLattice.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNeZeroOfIsLattice.lean#L24-L29

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsClassRepsMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNeZeroOfIsLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module nonZeroDivisors
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.RankOne
open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.HermitianLattices.Ext.L3.RankOne.span_eq_top_of_ne_zero {A : Submodule (𝓞 K) K} {a : K} (ha : a ∈ A) (h0 : a ≠ 0) :
    Submodule.span K (A : Set K) = ⊤ := by sorry
