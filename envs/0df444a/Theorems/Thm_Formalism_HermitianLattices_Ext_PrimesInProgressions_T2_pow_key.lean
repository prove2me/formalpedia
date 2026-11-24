-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_T2_pow_key
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.pow_key
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:12.353139+00:00
-- url     : https://prove2.me/theorems/2db4765d-6c94-4800-977f-33c720ccaf21
-- title:
--   T2: pow key
-- statement:
--   The T2 construction uses the pow key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExistsFarFromPoints.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/ExistsFarFromPoints.lean#L9-L18

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExistsFarFromPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.T2

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.T2.pow_key (x : ℝ) (hx0 : 0 < x) (a k : ℕ) (hka : k ≤ a) :
    x ^ (a + k) ≤ (5 * x) ^ a * (x / 5) ^ k := by sorry
