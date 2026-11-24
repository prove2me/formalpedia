-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_C2_inert_alg
-- name    : Formalism.HermitianLattices.Ext.L3.C2.inert_alg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:46:02.729966+00:00
-- url     : https://prove2.me/theorems/318e3483-41d6-41dc-a5a2-5d002ffbdcf7
-- title:
--   C2: inert alg
-- statement:
--   The C2 construction uses the inert alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountEqEulerFacInert.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormRepCountEqEulerFacInert.lean#L30-L36

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

theorem Formalism.HermitianLattices.Ext.L3.C2.inert_alg (q : ℝ) (hq : q ≠ 0) (M : ℕ) (hM : 1 ≤ M) :
    q ^ (M - 1) * (q ^ M - (-1) ^ M) = q ^ (2 * M - 1) * (1 - (-1 : ℝ) ^ M * q ^ (-(M : ℤ))) := by sorry
