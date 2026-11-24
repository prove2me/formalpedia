-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_horiz_num
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_horiz_num
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:38.288245+00:00
-- url     : https://prove2.me/theorems/9452eb85-0e1d-4fc9-a054-58376a7ece3b
-- title:
--   Primes In Progressions: exm horiz num
-- statement:
--   The Primes In Progressions construction uses the exm horiz num property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplMainA.lean#L118-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplMainA.lean#L118-L150

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_horiz_num (G N T T' y l : ℝ) (hG : 0 ≤ G) (hN0 : 0 ≤ N) (hN : N ≤ G * (T * l ^ 2))
    (hT : 2 ≤ T) (hT' : T ≤ T') (hy : 2 ≤ y) (hl : 1 ≤ l) :
    1 / (2 * Real.pi * y) * (3 * (N + 1) * (Real.exp 1 * y) / T' ^ 2) ≤
      3 * (G + 1) * (Real.log y * l ^ 2 / T) := by sorry
