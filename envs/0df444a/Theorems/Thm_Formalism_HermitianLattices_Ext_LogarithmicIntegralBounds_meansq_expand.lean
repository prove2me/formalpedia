-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_meansq_expand
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.meansq_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:47.437166+00:00
-- url     : https://prove2.me/theorems/a2ffdc9b-d97f-4571-b8e8-fe4f18b80ddb
-- title:
--   Logarithmic Integral Bounds: meansq expand
-- statement:
--   The Logarithmic Integral Bounds construction uses the meansq expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqMainA.lean#L9-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqMainA.lean#L9-L46

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqMainA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.meansq_expand (PP I : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (κ : ℕ → ℂ)
    (hκ : ∀ n, ‖κ n‖ ≤ 1) (J : ℕ → ℕ → ℤ) :
    (∑ q ∈ PP, ‖∑ n ∈ I, ((c n : ℝ) : ℂ) * κ n * ((J n q : ℤ) : ℂ)‖ ^ 2) ≤
      ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * |∑ q ∈ PP, ((J n q * J n' q : ℤ) : ℝ)| := by sorry
