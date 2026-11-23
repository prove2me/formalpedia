-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BoxSum_absNorm_eq_prod
-- name    : Formalism.HermitianLattices.Ext.L3.BoxSum.absNorm_eq_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:14.566833+00:00
-- url     : https://prove2.me/theorems/6178c537-9683-4719-b2f2-86d6ca17b6e8
-- title:
--   Box Sum: abs Norm eq prod
-- statement:
--   The Box Sum construction uses the abs Norm eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AbsNormEqProdOfMem.lean#L42-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AbsNormEqProdOfMem.lean#L42-L54

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

theorem Formalism.HermitianLattices.Ext.L3.BoxSum.absNorm_eq_prod [IsTotallyReal F] (n : 𝓞 F) :
    (Ideal.absNorm (Ideal.span {n}) : ℝ) = ∏ w : {w : InfinitePlace F // w.IsReal}, |rEmb w n| := by sorry
