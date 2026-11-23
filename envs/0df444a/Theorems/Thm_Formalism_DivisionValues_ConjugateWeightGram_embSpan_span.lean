-- Prove2me | Theorems.Thm_Formalism_DivisionValues_ConjugateWeightGram_embSpan_span
-- name    : Formalism.DivisionValues.ConjugateWeightGram.embSpan_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:12:22.901876+00:00
-- url     : https://prove2.me/theorems/fabc627a-a193-4b51-8c11-1e3d390fe6cc
-- title:
--   Conjugate Weight Gram: emb Span span
-- statement:
--   The Conjugate Weight Gram construction uses the emb Span span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ConjugateWeightLatticeOfGeneral.lean#L633-L650
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/ConjugateWeightLatticeOfGeneral.lean#L633-L650

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_JwConj
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DualMu
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open RationalHermitianForm
open Formalism.DivisionValues.ConjugateWeightGram

theorem Formalism.DivisionValues.ConjugateWeightGram.embSpan_span {K : Type} [Field K] {n d : ℕ} (τ : K →+* ℂ) (z : Fin d → Fin n → K) :
    embSpan τ (Submodule.span K (Set.range z)) =
      Submodule.span ℂ (Set.range fun c => (fun i => τ (z c i) : Fin n → ℂ)) := by sorry
