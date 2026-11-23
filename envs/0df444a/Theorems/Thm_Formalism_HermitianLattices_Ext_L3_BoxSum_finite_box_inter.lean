-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_finite_box_inter
-- name    : Formalism.HermitianLattices.Ext.L3.BoxSum.finite_box_inter
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:52:20.562368+00:00
-- url     : https://prove2.me/theorems/61ef60dc-3bbb-4b68-8ec4-89727efac154
-- title:
--   Box Sum: finite box inter
-- statement:
--   The Box Sum construction uses the finite box inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoSumCoset.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/TendstoSumCoset.lean#L12-L13

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemIdealLatticeIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_TendstoSumCoset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter Topology
open scoped Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BoxSum
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem Formalism.HermitianLattices.Ext.L3.BoxSum.finite_box_inter (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ) (A : Set (𝓞 F)) :
    {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ A}.Finite := by sorry
