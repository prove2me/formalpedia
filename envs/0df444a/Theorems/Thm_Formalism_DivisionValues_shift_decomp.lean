-- Prove2me | Theorems.Thm_Formalism_DivisionValues_shift_decomp
-- name    : Formalism.DivisionValues.shift_decomp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T00:11:11.426085+00:00
-- url     : https://prove2.me/theorems/85074370-db93-4ea1-8735-3f412aef18ff
-- title:
--   Division Values: shift decomp
-- statement:
--   The Division Values construction uses the shift decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/TwistedLatticeNaturality.lean#L328-L374
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/TwistedLatticeNaturality.lean#L328-L374

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DivIntoDual
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TwistedLatticeNaturality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
variable {K : Type} [Field K] [NumberField K] [StarRing K] {d : ℕ}

theorem Formalism.DivisionValues.shift_decomp (w : HeightOneSpectrum (𝓞 K)) :
    ∃ ϖ : 𝓞 K, ϖ ≠ 0 ∧ vw w (ϖ : K) = 1 ∧
      ∀ (n : ℕ) (x : 𝓞 K), x ≠ 0 → vw w (x : K) = n →
        ∃ t s : 𝓞 K, t ∉ w.asIdeal ∧ s ∉ w.asIdeal ∧ t * x = ϖ ^ n * s := by sorry
