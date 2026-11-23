-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_meansq_split
-- name    : Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.meansq_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:51.550969+00:00
-- url     : https://prove2.me/theorems/1d6e41c5-ed51-4784-bb8f-25d7156545d6
-- title:
--   Logarithmic Integral Bounds: meansq split
-- statement:
--   The Logarithmic Integral Bounds construction uses the meansq split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqMainB.lean#L9-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/MSqMainB.lean#L9-L36

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqMainB
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

theorem Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.meansq_split (I : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (r : ℕ → ℕ → ℕ) (A : ℕ → ℕ → ℝ)
    (P η : ℝ) (hP : 0 ≤ P) (hη : 0 ≤ η) (nstar : ℕ)
    (hA : ∀ n ∈ I, ∀ n' ∈ I, A n n' ≤ P)
    (hA' : ∀ n ∈ I, ∀ n' ∈ I, r n n' ≠ 1 → r n n' ≠ nstar → A n n' ≤ η * P) :
    ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * A n n' ≤
      ((∑ n ∈ I, ∑ n' ∈ I, if r n n' = 1 then c n * c n' else 0) +
        (∑ n ∈ I, ∑ n' ∈ I, if r n n' = nstar then c n * c n' else 0) + η * (∑ n ∈ I, c n) ^ 2) * P := by sorry
