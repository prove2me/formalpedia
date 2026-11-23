-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_log_le
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_log_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:19:43.752949+00:00
-- url     : https://prove2.me/theorems/fb035b0a-509a-43ea-a4d1-db6acd0be0f8
-- title:
--   Primes In Progressions: exm log le
-- statement:
--   The Primes In Progressions construction uses the exm log le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplMainA.lean#L39-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplMainA.lean#L39-L50

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplMainA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_log_le (M T u : ℝ) (hM : 3 ≤ M) (hT : 2 ≤ T) (hu0 : 0 ≤ u) (hu : u ≤ T + 1) :
    Real.log (M * (u + 2)) ≤ 2 * Real.log (M * T) := by sorry
