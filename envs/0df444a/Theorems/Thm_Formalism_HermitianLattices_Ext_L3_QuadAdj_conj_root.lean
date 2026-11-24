-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_QuadAdj_conj_root
-- name    : Formalism.HermitianLattices.Ext.L3.QuadAdj.conj_root
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:50.318478+00:00
-- url     : https://prove2.me/theorems/5b86167c-dc89-4989-838b-db94b75a3aff
-- title:
--   Quad Adj: conj root
-- statement:
--   The Quad Adj construction uses the conj root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandDA.lean#L86-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandDA.lean#L86-L86

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandDA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Polynomial
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.QuadAdj
variable {F : Type*} [Field F] (c : F)

theorem Formalism.HermitianLattices.Ext.L3.QuadAdj.conj_root : conj c (AdjoinRoot.root _) = -AdjoinRoot.root _ := by sorry
