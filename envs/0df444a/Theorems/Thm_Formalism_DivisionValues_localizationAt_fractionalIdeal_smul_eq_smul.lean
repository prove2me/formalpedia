-- Prove2me | Theorems.Thm_Formalism_DivisionValues_localizationAt_fractionalIdeal_smul_eq_smul
-- name    : Formalism.DivisionValues.localizationAt_fractionalIdeal_smul_eq_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:23:37.567804+00:00
-- url     : https://prove2.me/theorems/b5530bbc-1eb5-4b32-8cfe-434cc9e7e569
-- title:
--   Division Values: localization At fractional Ideal smul eq smul
-- statement:
--   The Division Values construction uses the localization At fractional Ideal smul eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/TwistedLatticeNaturality.lean#L547-L572
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/TwistedLatticeNaturality.lean#L547-L572

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

theorem Formalism.DivisionValues.localizationAt_fractionalIdeal_smul_eq_smul (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0)
    (w : HeightOneSpectrum (𝓞 K)) (N : Submodule (𝓞 K) (Fin d → K))
    {a : K} (ha : a ≠ 0) (hv : vw w a = FractionalIdeal.count K w I) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.HermitianLatticesTheory.idealSmul (I : Submodule (𝓞 K) K) N) =
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (smulLat a N) := by sorry
