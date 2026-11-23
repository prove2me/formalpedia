-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_BernoulliSumsFrobeniusOrbits_sum_card
-- name    : Formalism.FrobeniusOrbits.BernoulliSumsFrobeniusOrbits.sum_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:58.042894+00:00
-- url     : https://prove2.me/theorems/055b9bc8-629e-4413-90d4-076bf8f89286
-- title:
--   Bernoulli Sums Frobenius Orbits: sum card
-- statement:
--   The Bernoulli Sums Frobenius Orbits construction uses the sum card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickFrames.lean#L12-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickFrames.lean#L12-L23

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickFrames
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.BernoulliSumsFrobeniusOrbits
variable {α : Type*} [Fintype α]

theorem Formalism.FrobeniusOrbits.BernoulliSumsFrobeniusOrbits.sum_card (δ : ℝ) (f : ℕ → ℝ) :
    ∑ T : Finset α, bern δ T * f T.card =
      ∑ k ∈ range (Fintype.card α + 1),
        (bernsteinPolynomial ℝ (Fintype.card α) k).eval δ * f k := by sorry
