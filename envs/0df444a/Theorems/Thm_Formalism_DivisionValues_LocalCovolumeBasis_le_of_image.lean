-- Prove2me | Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_le_of_image
-- name    : Formalism.DivisionValues.LocalCovolumeBasis.le_of_image
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:13:52.447282+00:00
-- url     : https://prove2.me/theorems/e1272c35-cbea-41c4-99cc-744871f61ce9
-- title:
--   Local Covolume Basis: le of image
-- statement:
--   The Local Covolume Basis construction uses the le of image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/LcvBasis.lean#L106-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/LcvBasis.lean#L106-L119

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

theorem Formalism.DivisionValues.LocalCovolumeBasis.le_of_image {A N M1 M2 : Submodule (𝓞 K) V} (hN2 : N ≤ M2) (h1A : M1 ≤ A)
    (himg : (N.comap A.subtype).mkQ '' (A.subtype ⁻¹' (M1 : Set V)) =
      (N.comap A.subtype).mkQ '' (A.subtype ⁻¹' (M2 : Set V))) : M1 ≤ M2 := by sorry
