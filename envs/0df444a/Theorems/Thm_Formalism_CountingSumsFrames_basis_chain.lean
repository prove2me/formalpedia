-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_basis_chain
-- name    : Formalism.CountingSumsFrames.basis_chain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:10.538721+00:00
-- url     : https://prove2.me/theorems/015f2065-4870-4802-a304-283352500594
-- title:
--   Counting Sums Frames: basis chain
-- statement:
--   The Counting Sums Frames construction uses the basis chain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1325-L1367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1325-L1367

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Finset

theorem Formalism.CountingSumsFrames.basis_chain {K V : Type} [Field K] [AddCommGroup V] [Module K V] (A B : Submodule K V) (hAB : A ≤ B)
    [FiniteDimensional K B] (e : V) (he : e ∈ A) :
    ∃ b : Finset V, ((b : Set V) ⊆ (B : Set V)) ∧ LinearIndepOn K id (b : Set V) ∧
      ((B : Set V) ⊆ Submodule.span K (b : Set V)) ∧ (e ≠ 0 → e ∈ b) ∧
      ((A : Set V) ⊆ Submodule.span K ((b : Set V) ∩ (A : Set V))) ∧
      ∀ [DecidablePred (· ∈ A)], (b.filter (· ∈ A)).card = Module.finrank K A := by sorry
