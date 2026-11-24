-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_degree_le_of_mem_antidiagonal
-- name    : Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.degree_le_of_mem_antidiagonal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:48.469186+00:00
-- url     : https://prove2.me/theorems/d9c0aae8-dcfd-4e5a-bdc4-977d8462c320
-- title:
--   Integral Mv Polynomial Lemmas: degree le of mem antidiagonal
-- statement:
--   The Integral Mv Polynomial Lemmas construction uses the degree le of mem antidiagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/DegreeLeOfMemAntidiagonal.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/DegreeLeOfMemAntidiagonal.lean#L37-L41

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

theorem Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.degree_le_of_mem_antidiagonal [DecidableEq σ] {d : σ →₀ ℕ} {x : (σ →₀ ℕ) × (σ →₀ ℕ)}
    (hx : x ∈ Finset.HasAntidiagonal.antidiagonal d) : x.1.degree ≤ d.degree := by sorry
