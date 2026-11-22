-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WA_exists_norm_one_mul_mem
-- name    : Formalism.HermitianLattices.Ext.L3.WA.exists_norm_one_mul_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:37:17.849858+00:00
-- url     : https://prove2.me/theorems/6d59f171-ecfe-4af7-a4eb-688d13e49b33
-- title:
--   WA: exists norm one mul mem
-- statement:
--   The WA construction uses the exists norm one mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNormOneOfPair.lean#L34-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsNormOneOfPair.lean#L34-L73

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNormOneOfPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WA
variable {K : Type*} [Field K] [StarRing K]
variable {S : Subring K}

theorem Formalism.HermitianLattices.Ext.L3.WA.exists_norm_one_mul_mem (hS : IsHermSemilocal S) {a : K} (ha : star a * a ∈ S) :
    ∃ b : K, star b * b = 1 ∧ a * b ∈ S := by sorry
