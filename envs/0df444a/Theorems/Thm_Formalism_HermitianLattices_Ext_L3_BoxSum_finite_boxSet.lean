-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_finite_boxSet
-- name    : Formalism.HermitianLattices.Ext.L3.BoxSum.finite_boxSet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:49:10.025798+00:00
-- url     : https://prove2.me/theorems/4926a90c-c6cf-4a1c-9793-b378e6ac2f8c
-- title:
--   Box Sum: finite box Set
-- statement:
--   The Box Sum construction uses the finite box Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AbsNormEqProdOfMem.lean#L69-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AbsNormEqProdOfMem.lean#L69-L83

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_DifferentIdealEqTop
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AbsNormEqProdOfMem
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

theorem Formalism.HermitianLattices.Ext.L3.BoxSum.finite_boxSet (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ) :
    (boxSet K F T).Finite := by sorry
