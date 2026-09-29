-- Prove2me | Theorems.Thm_CerednikDrinfeld_Mumford_exists_periodField_completion
-- name    : CerednikDrinfeld.Mumford.exists_periodField_completion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/5668bf6b-8444-5ddf-9968-db91979528a3
-- title:
--   Inertia-fixed subfield of a completion of ℚ̄ as a period field
-- statement:
--   Let $r$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` lying over $r$ in the sense that the image of $r$ lies in the nonunits of $A$. Write $C_A$ for the completion `A.valuation.Completion` of $\overline{\mathbb Q}$ with respect to the valuation attached to $A$, equipped with its valuation `Valued.v` and with the induced action of the decomposition subgroup of $A$ over $\mathbb Q$. The assertion is that there exist an intermediate field $K$ of the extension $C_A/\mathbb Q$ and a group homomorphism $\mathrm{ord} : K^\times \to \mathbb Z$ (written as an additive monoid homomorphism out of `Additive (↥K)ˣ`) with the following four properties. First, for every $k \in K^\times$ one has $v(k) = v(r)^{\mathrm{ord}(k)}$ in the value group of $C_A$, the exponent being an integer. Second, for every element $\sigma$ of the decomposition subgroup whose underlying $\mathbb Q$-algebra automorphism of $\overline{\mathbb Q}$ lies in the image of the inertia subgroup under the inclusion of the decomposition subgroup, and for every $\mathbb Q$-algebra automorphism $s$ of $C_A$ with $s(c) = \sigma \cdot c$ for all $c \in C_A$, every element of $K$ is fixed by $s$. Third, for every $n > 0$ with $r \nmid n$, every $k \in K^\times$ with $\mathrm{ord}(k) = 0$ admits an $n$-th root in $K^\times$. Fourth, $K$ is maximal with the second property: any $c \in C_A$ fixed by every such automorphism $s$ of $C_A$ arising from an inertia element belongs to $K$.
--
--   This packages the inertia-fixed subfield of the completion of $\overline{\mathbb Q}$ at a place above $r$ as a "period field": a valued field with a $\mathbb Z$-valued order map normalised by $v(r)$, fixed pointwise by inertia, with roots of order-zero units of all degrees prime to $r$, and maximal for inertia-fixedness. It supplies the field datum required of a Mumford period uniformisation in the Čerednik–Drinfeld setting, and is used by [`AlgebraicCurve.Pic0.exists_periodDatum_Q_mul_period_eq_one_of_mumfordQuotient`](thm.html#AlgebraicCurve.Pic0.exists_periodDatum_Q_mul_period_eq_one_of_mumfordQuotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Mumford_exists_periodField_completion.lean

import Definitions.Def_CerednikDrinfeld_MumfordUniformization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford ModularCurve

theorem CerednikDrinfeld.Mumford.exists_periodField_completion
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ∃ K : IntermediateField ℚ A.valuation.Completion, ∃ ord : Additive (↥K)ˣ →+ ℤ,
      (∀ k : (↥K)ˣ, Valued.v (((k : ↥K) : A.valuation.Completion)) =
        Valued.v ((r : ℕ) : A.valuation.Completion) ^ (ord (Additive.ofMul k))) ∧
      (∀ σ : ↥(A.decompositionSubgroup ℚ),
        (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
        ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ c, s c = σ • c) →
          ∀ k : ↥K, s (k : A.valuation.Completion) = (k : A.valuation.Completion)) ∧
      (∀ n : ℕ, 0 < n → ¬ r ∣ n → ∀ k : (↥K)ˣ, ord (Additive.ofMul k) = 0 → ∃ k' : (↥K)ˣ, k' ^ n = k) ∧
      (∀ c : A.valuation.Completion,
        (∀ σ : ↥(A.decompositionSubgroup ℚ),
          (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A.inertiaSubgroupIn ℚ →
          ∀ s : A.valuation.Completion ≃ₐ[ℚ] A.valuation.Completion, (∀ x, s x = σ • x) → s c = c) → c ∈ K) := by sorry
