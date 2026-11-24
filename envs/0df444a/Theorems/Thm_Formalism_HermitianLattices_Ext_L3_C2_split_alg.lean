-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_C2_split_alg
-- name    : Formalism.HermitianLattices.Ext.L3.C2.split_alg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:46:21.645593+00:00
-- url     : https://prove2.me/theorems/6b0d3c40-eecf-4305-a439-bd2341e3386e
-- title:
--   C2: split alg
-- statement:
--   The C2 construction uses the split alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountEqEulerFacInert.lean#L38-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountEqEulerFacInert.lean#L38-L44

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountSplitOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountPowSuccInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
open Formalism.HermitianLattices.Ext.L3.C2

theorem Formalism.HermitianLattices.Ext.L3.C2.split_alg (q : ℝ) (hq : q ≠ 0) (M : ℕ) (hM : 1 ≤ M) :
    q ^ (2 * M - 1) - q ^ (M - 1) = q ^ (2 * M - 1) * (1 - q ^ (-(M : ℤ))) := by sorry
