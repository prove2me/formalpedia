-- Prove2me | Theorems.Thm_ExactLearningSeparation678_Randomized_Supplement_theorem_1_4
-- name    : ExactLearningSeparation678.Randomized.Supplement.theorem_1_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:32:11.131321+00:00
-- url     : https://prove2.me/theorems/adf3e7c1-96e5-437c-b523-10b903c660aa
-- title:
--   Theorem 1.4 (companion theorem) — $D(C)=\Omega(Q(C)^3\log N)$ with $Q(C)=\omega(1)$
-- statement:
--   Let $C_q$ ($q\ge2$) be the bilinear hidden-block classes of Definition 2.1 on the domain $X_q=[q^2]\times\mathbb F_2^q\times\mathbb F_2^q$, of size $N_q=q^2\,2^{2q}$. Then $Q(C_q)\to\infty$, and there are an absolute $c>0$ and a threshold $q_0$ such that
--   $$D(C_q)\ge c\,Q(C_q)^3\log N_q\qquad(q\ge q_0).$$
--   Here $D$ is the deterministic and $Q$ the bounded-error quantum membership-query complexity of exactly learning the class. Divergence means that for every bound $B$ all sufficiently large $q$ have $Q(C_q)\ge B$.
--
--   This family witnesses the existence statement of Theorem 1.4, and it matches the Servedio–Gortler simulation $D(C)=O(Q(C)^3\log N)$, so that simulation is optimal.
--
--   **Formalization Note** The true coordinate count $N_q$ appears inside the logarithm (natural). The constant and the threshold precede $q$.
--
--   Differences from the source:
--   - encoding: there exists C ⊆ {0,1}^N with Q(C) = ω(1) and D(C) = Ω(Q(C)³ log N) → the explicit Definition 2.1 family C_q (q ≥ 2) with its true domain cardinality q²·2^(2q), Q(C_q) → ∞, and one c > 0 and one threshold for all later q; reason: the proof supplies this witness family; the explicit quantifiers retain the entire existential asymptotic conclusion
--   - encoding: [q²], F₂^q, and Boolean values xᵀAy → Fin (q^2), Fin q → ZMod 2, and decide (b′ = b ∧ x ⬝ᵥ A y = 1); reason: a relabeling of the same domain and concepts
--   - encoding: logarithms of unspecified base → natural logarithm Real.log; reason: a change of base is absorbed into the absolute constant
--   - encoding: D(C): deterministic learner identifying the target with certainty → least worst-case depth of a DecisionTree whose output equals c for every c ∈ C; reason: the published deterministic decision-tree model
-- source:
--   Srinivasan Arunachalam, Amin Shiraz Gilani, Nikhil S. Mande, STOC 2027 submission #678 (October 2026), Theorem 1.4, p.3; Definition 2.1, p.13; §§2.2–2.4, pp.13–14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/678.pdf

import Definitions.Def_ExactLearningSeparation678_Randomized_Supplement_Models

open Classical
set_option autoImplicit false

namespace ExactLearningSeparation678.Randomized.Supplement

open QAlgorithms.Learning

/-- Theorem 1.4, p.3 (repeated p.14), for the witness family `C_q` of Definition 2.1, `q ≥ 2`:
the true domain size is `N_q = q²·2^{2q}`, `Q(C_q) → ∞`, and one absolute `c > 0` and one
threshold give `D(C_q) ≥ c · Q(C_q)³ · log N_q` for every later `q`. Natural logarithm. -/
theorem theorem_1_4 :
    (∀ q : ℕ, 2 ≤ q → Fintype.card (BilinDomain q) = q ^ 2 * 2 ^ (2 * q)) ∧
    (∀ B : ℕ, ∃ M : ℕ, ∀ q : ℕ, 2 ≤ q → M ≤ q →
      B ≤ quantumExactComplexity (bilinClass q)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ q : ℕ, 2 ≤ q → q₀ ≤ q →
      c * (quantumExactComplexity (bilinClass q) : ℝ) ^ 3 *
          Real.log (Fintype.card (BilinDomain q) : ℝ) ≤
        (detExactComplexity (bilinClass q) : ℝ)) := by sorry

end ExactLearningSeparation678.Randomized.Supplement
