-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
-- name    : AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/876357e9-72ce-5884-ab04-9844d74c85b8
-- title:
--   Branch valuation rings as localisations of the finite chart
-- statement:
--   Let $R$ be a discrete valuation ring (a domain), $K_0$ a fraction field of $R$, and $F$ a field that is an algebra over both $R$ and $K_0$ compatibly, with a distinguished element $j \in F$ assumed non-zero and transcendental over $R$; assume further that $F$ is finite-dimensional and separable over the intermediate field $K_0(j) =$ `IntermediateField.adjoin K₀ {j}`. Write $A =$ `chartAlgFin R F j` for the subalgebra of $F$ consisting of the elements integral over $R[j] =$ `Algebra.adjoin R {j}`, i.e. the integral closure of $R[j]$ in $F$. Let $V$ be a valuation subring of $F$ such that the image of $R$ lies in $V$, every element of the maximal ideal of $R$ maps into the non-units of $V$, and for every $P \in R[X]$ whose reduction modulo the maximal ideal of $R$ is non-zero both $P(j)$ and $P(j)^{-1}$ lie in $V$ (that is, $P(j) \in V^\times$). The conclusion has three parts. First, $A \subseteq V$. Second, there is a prime ideal $\mathfrak{P}$ of $A$ of height $1$ such that an element of $A$ lies in $\mathfrak{P}$ precisely when it is a non-unit of $V$, such that the image in $A$ of every element of the maximal ideal of $R$ lies in $\mathfrak{P}$, and such that an element $f \in F$ lies in $V$ precisely when $f \cdot b = a$ for some $a, b \in A$ with $b \notin \mathfrak{P}$; thus $V$ is the localisation of $A$ at $\mathfrak{P}$ inside $F$. Third, for every valuation subring $V'$ of $F$ satisfying the same three hypotheses (containing the image of $R$, sending the maximal ideal of $R$ into its non-units, and making $P(j)$ a unit for every $P$ with non-zero reduction) and with $V' \neq V$, there exists $b \in A$ that is a non-unit of $V'$ but a unit of $V$.
--
--   This identifies the branch valuation rings attached to a two-chart integral model over a discrete valuation ring with the local rings of the finite chart at the centres of those valuations, the centres being height-one primes above the uniformiser, and shows that distinct branches have distinct, mutually non-dominating centres. It is the converse direction to the passage from a minimal prime over the uniformiser to a valuation ring, and is used to match minimal primes of the uniformiser with centres and in the special-fibre analysis of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.le_and_height_eq_one_and_exists_div_of_valuationSubring_of_transcendental
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (V : ValuationSubring F)
    (hVA : ∀ a : R, algebraMap R F a ∈ V)
    (hVm : ∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R F a ∈ V.nonunits)
    (hVj : ∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) :

    (∀ b : ↥(chartAlgFin R F j), (b : F) ∈ V) ∧

    (∃ 𝔓 : Ideal ↥(chartAlgFin R F j), 𝔓.IsPrime ∧ 𝔓.height = 1 ∧
      (∀ b : ↥(chartAlgFin R F j), b ∈ 𝔓 ↔ (b : F) ∈ V.nonunits) ∧
      (∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R ↥(chartAlgFin R F j) a ∈ 𝔓) ∧

      (∀ f : F, f ∈ V ↔ ∃ a b : ↥(chartAlgFin R F j), b ∉ 𝔓 ∧ f * (b : F) = (a : F))) ∧

    (∀ V' : ValuationSubring F,
      (∀ a : R, algebraMap R F a ∈ V') →
      (∀ a ∈ IsLocalRing.maximalIdeal R, algebraMap R F a ∈ V'.nonunits) →
      (∀ P : Polynomial R, P.map (IsLocalRing.residue R) ≠ 0 →
        Polynomial.aeval j P ∈ V' ∧ (Polynomial.aeval j P)⁻¹ ∈ V') →
      V ≠ V' →
      ∃ b : ↥(chartAlgFin R F j), (b : F) ∈ V'.nonunits ∧ (b : F) ∉ V.nonunits) := by sorry
