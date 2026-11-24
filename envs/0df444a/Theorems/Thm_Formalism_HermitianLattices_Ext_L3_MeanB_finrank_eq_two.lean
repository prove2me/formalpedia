-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_finrank_eq_two
-- name    : Formalism.HermitianLattices.Ext.L3.MeanB.finrank_eq_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:47:11.119825+00:00
-- url     : https://prove2.me/theorems/e3f07f24-e77f-4fef-83a9-6d3656e6a033
-- title:
--   Mean B: finrank eq two
-- statement:
--   The Mean B construction uses the finrank eq two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/StarAlgebraMap.lean#L23-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/StarAlgebraMap.lean#L23-L58

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulSubOneMemPow
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.MeanB
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem Formalism.HermitianLattices.Ext.L3.MeanB.finrank_eq_two (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) : finrank F K = 2 := by sorry
