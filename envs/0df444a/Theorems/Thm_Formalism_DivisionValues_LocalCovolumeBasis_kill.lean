-- Prove2me | Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_kill
-- name    : Formalism.DivisionValues.LocalCovolumeBasis.kill
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:13:53.390401+00:00
-- url     : https://prove2.me/theorems/7505067a-477b-4e7c-a035-93c90b2575e7
-- title:
--   Local Covolume Basis: kill
-- statement:
--   The Local Covolume Basis construction uses the kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/LcvBasis.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/LcvBasis.lean#L30-L35

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

theorem Formalism.DivisionValues.LocalCovolumeBasis.kill {N : Submodule (𝓞 K) V} {a : V} {p : Ideal (𝓞 K)} (hp : ∀ r, r ∈ p ↔ r • a ∈ N)
    {s : 𝓞 K} (hs : s ∈ p) {y : V} (hy : y ∈ N ⊔ Submodule.span (𝓞 K) {a}) : s • y ∈ N := by sorry
