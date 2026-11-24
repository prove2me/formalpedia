-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_alg
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_alg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:23.497997+00:00
-- url     : https://prove2.me/theorems/80fd3ccb-d62e-46f2-896a-f999de9832c4
-- title:
--   Primes In Progressions: exm alg
-- statement:
--   The Primes In Progressions construction uses the exm alg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplMainA.lean#L9-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplMainA.lean#L9-L22

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_alg (S Ifull R Lf Bt Tp K D Sg : ℂ) (y : ℝ) (hy : 0 < y)
    (hS : S = (1 / (2 * Real.pi) : ℂ) * Ifull)
    (hrect : Bt - Tp + I * R - I * Lf = 2 * Real.pi * I * (K * y + D - Sg)) :
    S / y - K - D / y + Sg / y =
      (1 / (2 * Real.pi * y) : ℂ) * ((Ifull - R) + Lf + I * (Bt - Tp)) := by sorry
