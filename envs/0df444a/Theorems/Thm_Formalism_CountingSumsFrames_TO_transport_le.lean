-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_transport_le
-- name    : Formalism.CountingSumsFrames.TO.transport_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:13.795498+00:00
-- url     : https://prove2.me/theorems/3e9d36ec-f1a3-4d60-a027-7da1853e1e63
-- title:
--   TO: transport le
-- statement:
--   The TO construction uses the transport le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2828-L2876
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2828-L2876

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
  (Pi : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
  (hPi : IsProjC L j0 e J M Pi)
  {ι : Type} [Fintype ι] [DecidableEq ι] (h : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]) (la : ι → Fin r → ℤ)
  (hh : ∀ i, (GA p L j0).IsHW (la i) (h i)) (hhC : ∀ i, h i ∈ Cset p L j0 J M)
  (hli : LinearIndependent ℚ_[p] h) (hsp : Cset p (r := r) L j0 J M ≤ ⨆ i, (GA p L j0).gS {h i})
include hPi hh hhC hli hsp

theorem Formalism.CountingSumsFrames.TO.transport_le (i0 : ι) (v : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hv : (GA p L j0).IsHW (la i0) v)
    (hvC : v ∈ Cset p L j0 J M) (hv0 : v ≠ 0) :
    Module.finrank ℚ_[p] (YYs L j0 J M (h i0)) ≤ Module.finrank ℚ_[p] (YYs L j0 J M v) := by sorry
