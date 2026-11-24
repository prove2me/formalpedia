-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_bigOp_int
-- name    : Formalism.CountingSumsFrames.TO.bigOp_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:01.961867+00:00
-- url     : https://prove2.me/theorems/78581f62-2c01-4fd5-b5dd-bc3905c61b25
-- title:
--   TO: big Op int
-- statement:
--   The TO construction uses the big Op int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2623-L2661
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2623-L2661

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
variable [NeZero r] (L : Letters N) (j0 e : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
  (Pi φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
  (hPi : IsProjC L j0 e J M Pi) (hφ : IsEqC L j0 J M φ)
include hPi
include hφ

theorem Formalism.CountingSumsFrames.TO.bigOp_int
    (hint : ∀ μ v, v ∈ Cset p L j0 J M → (GA p L j0).IsHW μ v → v ∈ IntPol p (Fin N × Fin r) →
      φ v ∈ IntPol p (Fin N × Fin r))
    (la : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ HWC p L j0 univ la ⊓ Pol p r L)
    (hxi : x ∈ IntPol p (Fin N × Fin r)) :
    ((p : ℚ_[p]) ^ e) • bigOp L j0 Pi φ x ∈ IntPol p (Fin N × Fin r) := by sorry
