-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exm_N_le
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_N_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:14.50255+00:00
-- url     : https://prove2.me/theorems/a21fe197-5fa5-4988-9b44-d980879e10fb
-- title:
--   Primes In Progressions: exm N le
-- statement:
--   The Primes In Progressions construction uses the exm N le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplMainA.lean#L57-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTExplMainA.lean#L57-L83

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.exm_N_le (κ C₁ C₂ M T δ : ℝ) (hκ : 0 < κ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hM : 3 ≤ M) (hT : 2 ≤ T)
    (_hδ0 : 0 < δ) (hδ : κ / (C₁ * (T + 1) * Real.log (M * (T + 2))) ≤ δ) :
    C₂ * (2 * Real.log (M * T)) / δ ≤ 6 * C₁ * C₂ / κ * (T * Real.log (M * T) ^ 2) := by sorry
