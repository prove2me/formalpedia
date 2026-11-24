-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_BernoulliSumsFrobeniusOrbits_sum_bern_var
-- name    : Formalism.FrobeniusOrbits.BernoulliSumsFrobeniusOrbits.sum_bern_var
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:54.368348+00:00
-- url     : https://prove2.me/theorems/a050a9eb-5831-482e-b384-721809e49c6d
-- title:
--   Bernoulli Sums Frobenius Orbits: sum bern var
-- statement:
--   The Bernoulli Sums Frobenius Orbits construction uses the sum bern var property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickFrames.lean#L35-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickFrames.lean#L35-L46

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

theorem Formalism.FrobeniusOrbits.BernoulliSumsFrobeniusOrbits.sum_bern_var (δ : ℝ) :
    ∑ T : Finset α, bern δ T * ((T.card : ℝ) - δ * Fintype.card α) ^ 2 =
      Fintype.card α * δ * (1 - δ) := by sorry
