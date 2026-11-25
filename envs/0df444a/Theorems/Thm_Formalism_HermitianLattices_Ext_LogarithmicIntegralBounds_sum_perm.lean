-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_sum_perm
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.sum_perm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:40:53.981663+00:00
-- url     : https://prove2.me/theorems/ef4cc1d1-a3a5-46b4-864c-d21859d9efc3
-- title:
--   Logarithmic Integral Bounds: sum perm
-- statement:
--   The Logarithmic Integral Bounds construction uses the sum perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqOrth.lean#L15-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqOrth.lean#L15-L31

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqOrth
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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.sum_perm {R : Type*} [AddCommMonoid R] (M c : ℕ) (hc : c.Coprime M) (S S' : Finset ℕ)
    (hS : ∀ b ∈ S, b < M) (hmap : ∀ b ∈ S, (c * b) % M ∈ S') (hcard : S'.card ≤ S.card) (f : ℕ → R) :
    ∑ b ∈ S', f b = ∑ b ∈ S, f ((c * b) % M) := by sorry
