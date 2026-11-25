-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_int_main
-- name    : Formalism.CountingSumsFrames.TO.int_main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:59.842232+00:00
-- url     : https://prove2.me/theorems/7e252212-17c5-4857-a8f3-6cc4eabc86d1
-- title:
--   TO: int main
-- statement:
--   The TO construction uses the int main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2064-L2147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2064-L2147

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.TO.int_main (L : Letters N) (ρ : Fin r) (e1 j0 : ℕ) (hj0 : j0 ≤ N) (hHP : HypP p L ρ e1) (hHW : HypW p (r := r) L e1)
    (Tm : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]) (K0 : ℕ)
    (hcomm : ∀ c d x, Tm (glAct p L j0 c d x) = glAct p L j0 c d (Tm x))
    (hhw : ∀ la : Fin r → ℤ, ∀ h ∈ HWC p L j0 univ la ⊓ Pol p r L, h ∈ IntPol p (Fin N × Fin r) →
      ((p : ℚ_[p]) ^ K0) • Tm h ∈ IntPol p (Fin N × Fin r)) :
    ∀ y ∈ PolZ p r L, ((p : ℚ_[p]) ^ (K0 + 2 * e1)) • Tm y ∈ IntPol p (Fin N × Fin r) := by sorry
