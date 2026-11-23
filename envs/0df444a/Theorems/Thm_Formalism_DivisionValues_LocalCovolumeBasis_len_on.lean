-- Prove2me | Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_len_on
-- name    : Formalism.DivisionValues.LocalCovolumeBasis.len_on
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:33.6288+00:00
-- url     : https://prove2.me/theorems/f48fd876-fee2-4090-95b4-eeca283b33b0
-- title:
--   Local Covolume Basis: len on
-- statement:
--   The Local Covolume Basis construction uses the len on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/LcvBasis.lean#L54-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/HermitianTwistDivisors/LcvBasis.lean#L54-L98

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

theorem Formalism.DivisionValues.LocalCovolumeBasis.len_on {N : Submodule (𝓞 K) V} {a : V} (q : Ideal (𝓞 K)) [hq : q.IsPrime]
    (hqmax : q.IsMaximal) (hp : ∀ r, r ∈ q ↔ r • a ∈ N) :
    Module.length (𝓞 K) (↥(localization₂ q (N ⊔ Submodule.span (𝓞 K) {a})) ⧸
      (localization₂ q N).comap (localization₂ q (N ⊔ Submodule.span (𝓞 K) {a})).subtype) = 1 := by sorry
