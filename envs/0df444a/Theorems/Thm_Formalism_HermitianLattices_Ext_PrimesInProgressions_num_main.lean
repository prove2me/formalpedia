-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_num_main
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.num_main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:57.157204+00:00
-- url     : https://prove2.me/theorems/137fd771-7dc5-49d4-a533-c9d12ef62a51
-- title:
--   Primes In Progressions: num main
-- statement:
--   The Primes In Progressions construction uses the num main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsmA.lean#L88-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTBAsmA.lean#L88-L158

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

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.num_main (cA κ C : ℝ) (hcA : 0 < cA) (hκ : 0 < κ) (hC : 0 < C) :
    ∃ C₀ B : ℝ, 0 ≤ C₀ ∧ 0 ≤ B ∧ ∀ M y : ℝ, 8 ≤ M → 2 ≤ y →
      C₀ * Real.log M * Real.log (Real.log M + 2) ≤ Real.log y →
      cA * Real.sqrt (Real.log y) < Real.log M →
      M * (4 * y * (C * ((M * M ^ (12 : ℝ)) ^ C * y ^ (-(κ / 2))
          + Real.log (2 * y) * Real.log (M * M ^ (12 : ℝ)) ^ 2 / M ^ (12 : ℝ))) / (M ^ 5)⁻¹
          + 4 * ((M ^ 5)⁻¹ * y + 1) * Real.log (2 * y))
        + 20 * (M ^ 5)⁻¹ * y + 2 * y * y ^ (-(κ / 2)) ≤ B * y * (M⁻¹ * M⁻¹) := by sorry
