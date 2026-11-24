-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_tail_num
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_tail_num
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:37.179593+00:00
-- url     : https://prove2.me/theorems/b43174c3-cc0c-4abd-be62-7d87f05f8f58
-- title:
--   Primes In Progressions: exm tail num
-- statement:
--   The Primes In Progressions construction uses the exm tail num property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplMainA.lean#L89-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplMainA.lean#L89-L116

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_tail_num (C₃ T T' y l : ℝ) (hC₃ : 0 ≤ C₃) (hT : 2 ≤ T) (hT' : T ≤ T') (hy : 2 ≤ y) (hl : 1 ≤ l) :
    1 / (2 * Real.pi * y) * (2 * (Real.log y + C₃) * (Real.exp 1 * y) / T') ≤
      (1 + 2 * C₃) * (Real.log y * l ^ 2 / T) := by sorry
