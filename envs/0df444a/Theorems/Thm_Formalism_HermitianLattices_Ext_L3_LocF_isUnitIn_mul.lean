-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocF_isUnitIn_mul
-- name    : Formalism.HermitianLattices.Ext.L3.LocF.isUnitIn_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:09:22.712943+00:00
-- url     : https://prove2.me/theorems/cef5e3ea-f4bd-4de8-a01f-7f0c6cfbf674
-- title:
--   Loc F: is Unit In mul
-- statement:
--   The Loc F construction uses the is Unit In mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LinearIndependentOfGramDetNeZero.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LinearIndependentOfGramDetNeZero.lean#L17-L18

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityRatio
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthUnitFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_GmapLocEqOfFrame
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LinearIndependentOfGramDetNeZero
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocF
open Formalism.HermitianLattices.Ext.L3.WA
variable {K : Type*} [Field K] {S : Subring K}

theorem Formalism.HermitianLattices.Ext.L3.LocF.isUnitIn_mul {a b : K} (ha : IsUnitIn S a) (hb : IsUnitIn S b) : IsUnitIn S (a * b) := by sorry
