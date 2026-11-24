-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_norm
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:27.226598+00:00
-- url     : https://prove2.me/theorems/88cf0ae7-8dd2-4c90-b2cf-9ffa6089165f
-- title:
--   Primes In Progressions: exm norm
-- statement:
--   The Primes In Progressions construction uses the exm norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplMainA.lean#L24-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplMainA.lean#L24-L37

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_norm (Ifull R Lf Bt Tp : ℂ) (y a b c d : ℝ) (hy : 0 < y)
    (ha : ‖Ifull - R‖ ≤ a) (hb : ‖Lf‖ ≤ b) (hc : ‖Bt‖ ≤ c) (hd : ‖Tp‖ ≤ d) :
    ‖(1 / (2 * Real.pi * y) : ℂ) * ((Ifull - R) + Lf + I * (Bt - Tp))‖ ≤
      1 / (2 * Real.pi * y) * (a + b + (c + d)) := by sorry
