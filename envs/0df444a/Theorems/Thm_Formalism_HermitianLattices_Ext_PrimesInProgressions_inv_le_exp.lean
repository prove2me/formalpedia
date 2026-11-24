-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_inv_le_exp
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.inv_le_exp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:45.355594+00:00
-- url     : https://prove2.me/theorems/0d635e09-a142-42f7-a501-c038b85bac60
-- title:
--   Primes In Progressions: inv le exp
-- statement:
--   The Primes In Progressions construction uses the inv le exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsmA.lean#L74-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsmA.lean#L74-L86

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTBAsmA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.inv_le_exp {cA c M y : ℝ} (hcA : 0 < cA) (hc : 0 < c) (hc' : c ≤ cA ^ 2) (hM : 8 ≤ M) (hy : 2 ≤ y)
    (h : cA * Real.sqrt (Real.log y) < Real.log M) :
    M⁻¹ ≤ Real.exp (-(c * Real.log y / Real.log M)) := by sorry
