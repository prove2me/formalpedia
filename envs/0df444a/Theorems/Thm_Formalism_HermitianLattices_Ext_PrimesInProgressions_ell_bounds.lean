-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_ell_bounds
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.ell_bounds
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:16:38.751598+00:00
-- url     : https://prove2.me/theorems/1e4e6048-fd5b-5c84-9b43-126a7e7804a7
-- title:
--   Primes In Progressions: ell bounds
-- statement:
--   The Primes In Progressions construction uses the ell bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTZSumB.lean#L73-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTZSumB.lean#L73-L97

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DeuringHeilbronnM
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTZSumB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.ell_bounds (M : ℕ) (hM : 8 ≤ M) (A₁ : ℝ) (hA : 1 ≤ A₁) :
    2 ≤ Real.log M ∧ Real.log M ≤ Real.log ((M : ℝ) * ((M : ℝ) ^ A₁ + 3)) ∧
      Real.log ((M : ℝ) * ((M : ℝ) ^ A₁ + 3)) ≤ (A₁ + 2) * Real.log M := by sorry
