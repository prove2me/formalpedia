-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_degree_fst_lt
-- name    : Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.degree_fst_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:49.941808+00:00
-- url     : https://prove2.me/theorems/d684f35a-54d6-4d7b-ab59-9f439e6c649a
-- title:
--   Integral Mv Polynomial Lemmas: degree fst lt
-- statement:
--   The Integral Mv Polynomial Lemmas construction uses the degree fst lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/DegreeLeOfMemAntidiagonal.lean#L73-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/DegreeLeOfMemAntidiagonal.lean#L73-L78

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.IntegralMvPolynomialLemmas
variable {A : Type*} [CommRing A] {σ : Type*}

theorem Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.degree_fst_lt [DecidableEq σ] {d : σ →₀ ℕ} {x : (σ →₀ ℕ) × (σ →₀ ℕ)}
    (hx : x ∈ Finset.HasAntidiagonal.antidiagonal d) (h2 : x.2 ≠ 0) : x.1.degree < d.degree := by sorry
