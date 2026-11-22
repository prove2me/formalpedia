-- Prove2me | Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_key
-- name    : Formalism.DivisionValues.LocalCovolumeBasis.key
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:33:27.699292+00:00
-- url     : https://prove2.me/theorems/ec14cd27-829a-434c-ba60-cf5a5f28a677
-- title:
--   Local Covolume Basis: key
-- statement:
--   The Local Covolume Basis construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/LcvBasis.lean#L121-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/LcvBasis.lean#L121-L284

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Formalism.HermitianLatticesTheory
noncomputable section
open Formalism Formalism.DivisionValues Formalism.DivisionValues.LocalCovolumeBasis
variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]

theorem Formalism.DivisionValues.LocalCovolumeBasis.key (A : Submodule (𝓞 K) V) : ∀ (n : ℕ) (N : Submodule (𝓞 K) V), N ≤ A →
    N.toAddSubgroup.relIndex A.toAddSubgroup = n → n ≠ 0 →
    (∀ w : HeightOneSpectrum (𝓞 K), Module.length (𝓞 K)
      (↥(localization₂ w.asIdeal A) ⧸ (localization₂ w.asIdeal N).comap (localization₂ w.asIdeal A).subtype) ≠ ⊤) ∧
    (Function.support fun w : HeightOneSpectrum (𝓞 K) => locLen w.asIdeal A N).Finite ∧
    Real.log (n : ℝ) = ∑ᶠ w : HeightOneSpectrum (𝓞 K),
      Real.log (Ideal.absNorm w.asIdeal : ℝ) * (locLen w.asIdeal A N : ℝ) := by sorry
