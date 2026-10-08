-- Prove2me | Theorems.Thm_CvitanicKaratzas92_Optimality_theorem_10_1
-- name    : CvitanicKaratzas92.Optimality.theorem_10_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:24:00.334626+00:00
-- url     : https://prove2.me/theorems/7c619e67-f024-4bfc-92c1-04d65c9f78fe
-- title:
--   Theorem 10.1 — (B) financibility ⇔ (C) minimality ⇔ (D) dual optimality ⇔ (E) parsimony ⇒ (A) optimality; conversely (A) ⇒ (B)–(E) under (5.8), (8.25), (12.2)
-- statement:
--   Consider the market $\mathcal M$ of Cvitanić and Karatzas under the paper's standing assumptions (complete probability space, Brownian filtration, (2.3)–(2.5), (2.7), a nonempty closed convex constraint set $K$ with (4.3)–(4.4), utilities $U_1,U_2$ as in Section 6, and Assumption 6.2), and the constrained problem of maximizing $J(x;\pi,c)$ over $\mathcal A'(x)$. For a fixed initial capital $x>0$, conditions (A)–(E) are those of Section 10:
--
--   1. (A) *optimality* of a pair $(\hat\pi,\hat c)\in\mathcal A'(x)$, including the integrability (10.2);
--   2. (B) *financibility* of $(c_\lambda,\xi_\lambda)$: some portfolio $\hat\pi_\lambda$ with $(\hat\pi_\lambda,c_\lambda)\in\mathcal A'(x)$ has $\hat\pi_\lambda\in K$, $\delta(\lambda)+\hat\pi_\lambda^*\lambda=0$ and $X^{x,\hat\pi_\lambda,c_\lambda}=X_\lambda$;
--   3. (C) *minimality* of $\lambda$: $V_\lambda(x)$ equals the expected utility of $(c_\lambda,\xi_\lambda)$ and $V_\lambda(x)\le V_\nu(x)$ for all $\nu\in\mathcal D$;
--   4. (D) *dual optimality* of $\lambda$: $\tilde J(\mathcal Y_\lambda(x);\lambda)\le\tilde J(\mathcal Y_\lambda(x);\nu)$ for all $\nu\in\mathcal D$;
--   5. (E) *parsimony* of $\lambda$: $E[\int_0^TH_\nu c_\lambda\,dt+H_\nu(T)\xi_\lambda]\le x$ for all $\nu\in\mathcal D$;
--
--   where (B)–(E) concern a process $\lambda\in\mathcal D'$. **Theorem 10.1.** *Conditions (B)–(E) are equivalent, and imply (A) with $(\hat\pi,\hat c)=(\hat\pi_\lambda,c_\lambda)$. Conversely, condition (A) implies the existence of $\lambda\in\mathcal D'$ that satisfies (B)–(E) with $\hat\pi_\lambda\equiv\hat\pi$, provided that (5.8), (8.25) and (12.2) hold for $U_1(t,\cdot)$ and $U_2(\cdot)$.*
--
--   In symbols, for every $x>0$ and $\lambda\in\mathcal D'$,
--   $$(\mathrm B)\iff(\mathrm C)\iff(\mathrm D)\iff(\mathrm E)\implies(\mathrm A)\ \text{for}\ (\hat\pi_\lambda,c_\lambda),$$
--   and under (5.8), (8.25), (12.2), every pair satisfying (A) arises in this way from some $\lambda\in\mathcal D'$.
--
--   This is the focal result of the paper: the constrained problem is solved by finding the auxiliary market $\mathcal M_\lambda$ in which the unconstrained optimal policy happens to respect the constraint, and that market is characterized as the minimizer of a dual stochastic control problem (condition (D)), which leads to the dual problem of Section 12. By Remark 4.2, condition (4.4) is not used in proving the equivalences; it is kept here because the paper assumes it throughout.
--
--   **Formalization Note** $\mathcal Y_\lambda(x)$ is represented by a number $y>0$ with $\mathcal X_\lambda(y)=x$ (it exists and is unique for $\lambda\in\mathcal D'$). The first conjunct states the three equivalences and that every witness $(\hat\pi_\lambda,X)$ of (B) gives a triple $(\hat\pi_\lambda,c_\lambda,X)$ satisfying (A). The second states the converse: under (5.8) for $U_2$ and every $U_1(t,\cdot)$, (8.25) with common constants, and (12.2), every triple satisfying (A) admits $\lambda\in\mathcal D'$ and $y=\mathcal Y_\lambda(x)$ for which (C), (D), (E) hold and (B) holds with a portfolio equal to $\hat\pi$ $\ell\otimes P$-a.e. ("$\hat\pi_\lambda\equiv\hat\pi$"). The stochastic integral is an explicit Itô-integral operator binder, constrained only by the standing hypothesis that it integrates every locally square-integrable process; values of utility expectations are extended reals.
-- source:
--   Cvitanić and Karatzas, Convex Duality in Constrained Portfolio Optimization, Ann. Appl. Probab. 2 (1992), p. 786, Theorem 10.1 (conditions (A)–(E), pp. 785–786)

import Mathlib
import Definitions.Def_CvitanicKaratzas92_Optimality_Conditions

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace CvitanicKaratzas92.Optimality

/-- Cvitanić–Karatzas (1992), Theorem 10.1, p. 786. Conditions (B)–(E) on `λ ∈ 𝒟'` are
equivalent and imply (A) for `(π̂_λ, c_λ)`; conversely, under (5.8), (8.25) and (12.2), (A)
implies the existence of `λ ∈ 𝒟'` satisfying (B)–(E) with `π̂_λ ≡ π̂`. The number `y > 0` with
`𝒳_λ(y) = x` is `𝒴_λ(x)`. -/
theorem theorem_10_1 {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (T : ℝ≥0)
    (W : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (I : (ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) → ℝ≥0 → Ω → ℝ)
    (M : Market Ω d) (K : Set (EuclideanSpace ℝ (Fin d)))
    (U1 : ℝ≥0 → ℝ → ℝ) (U2 : ℝ → ℝ)
    (hS : Standing P 𝓕 T W I M K U1 U2) :
    (∀ x : ℝ, 0 < x → ∀ (lam : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (y : ℝ),
      IsD' P 𝓕 T I M K U1 U2 lam → 0 < y →
      calX P T I M K U1 U2 lam y = ENNReal.ofReal x →
      (CondB P 𝓕 T I M K U1 U2 lam y x ↔ CondC P 𝓕 T I M K U1 U2 lam y x) ∧
      (CondC P 𝓕 T I M K U1 U2 lam y x ↔ CondD P 𝓕 T I M K U1 U2 lam y) ∧
      (CondD P 𝓕 T I M K U1 U2 lam y ↔ CondE P 𝓕 T I M K U1 U2 lam y x) ∧
      ∀ (πhat : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (X : ℝ≥0 → Ω → ℝ),
        CondBWith P 𝓕 T I M K U1 U2 lam y x πhat X →
        CondA P 𝓕 T I M K U1 U2 x ⟨πhat, cNu I M K U1 lam y, X⟩) ∧
    ((∀ t ≤ T, Cond58 (U1 t)) → Cond58 U2 → Cond825 T U1 U2 →
      Cond122 P 𝓕 T I M K U1 U2 →
      ∀ x : ℝ, 0 < x → ∀ τ : Triple Ω d, CondA P 𝓕 T I M K U1 U2 x τ →
        ∃ (lam : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (y : ℝ),
          IsD' P 𝓕 T I M K U1 U2 lam ∧ 0 < y ∧
          calX P T I M K U1 U2 lam y = ENNReal.ofReal x ∧
          (∃ (πhat : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (X : ℝ≥0 → Ω → ℝ),
            CondBWith P 𝓕 T I M K U1 U2 lam y x πhat X ∧
            ∀ᵐ q ∂(lebP P T), πhat q.1.toNNReal q.2 = τ.π q.1.toNNReal q.2) ∧
          CondC P 𝓕 T I M K U1 U2 lam y x ∧
          CondD P 𝓕 T I M K U1 U2 lam y ∧
          CondE P 𝓕 T I M K U1 U2 lam y x) := by sorry

end CvitanicKaratzas92.Optimality
