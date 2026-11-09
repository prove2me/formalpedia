-- Prove2me | Theorems.Thm_CNFLearning873_Valiant_lemma_3_2
-- name    : CNFLearning873.Valiant.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T05:06:44.593543+00:00
-- url     : https://prove2.me/theorems/670bee21-70aa-46e3-95e5-249eb55ece5e
-- title:
--   Lemma 3.2 — satisfiability and local uniformity
-- statement:
--   Let $F$ be a CNF on $n$ Boolean variables with clause widths between positive integers $k_1\le k_2$, and variable degree at most the positive integer $d$. For an independent real parameter $t_{\rm LU}\ge k_2$, assume $2^{k_1}\ge2e d t_{\rm LU}$. Then $F$ is satisfiable and its uniform solution law satisfies
--
--   $$\forall v\in V,\quad\forall b\in\{0,1\},\quad \Pr_{X\sim\mu_F}(X_v=b)\le\tfrac12\exp(1/t_{\rm LU}).$$
--
--   This is the variable-width local uniformity result used for conditioned formulas. No hypothesis asserts satisfiability or any conditional marginal bound.
--
--   Differences from the source:
--   - encoding: finite Boolean variables and forbidden assignments → Fin n and published literal-sign clauses; reason: bijective relabeling and negation of literal signs preserve every clause and assignment
--   - encoding: uniform solution distribution → an existential proof of nonempty solutions followed by the published finite uniform law; reason: satisfiability is concluded and a probability law is never placed on an empty set
--   - encoding: max over the two Boolean values → one inequality for each Boolean value; reason: equivalent finite maximum bound
--   - encoding: positive width and degree conventions → 1 ≤ k₁ ≤ k₂ and 1 ≤ d; reason: makes the positive-integer source convention explicit; no k ≥ 100 restriction is introduced
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf, Lemma 3.2, printed p.12 = 1-based PDF p.12

import Definitions.Def_CNFLearning873_Valiant_SolutionLaw

namespace CNFLearning873.Valiant

/-- Lemma 3.2, p.12 = PDF p.12, Feng--Yu--Zhang, STOC 2027 submission #873
(October 2026). Satisfiability and both Boolean marginal bounds; variable widths.
The positive-width convention is made explicit. -/
theorem lemma_3_2 (n k₁ k₂ d : ℕ) (tLU : ℝ) (F : CNF n)
    (hk₁ : 1 ≤ k₁) (hwidth : k₁ ≤ k₂) (hd : 1 ≤ d)
    (hF : WidthBounds F k₁ k₂) (hdegree : DegreeBound F d)
    (ht : (k₂ : ℝ) ≤ tLU)
    (hLLL : 2 * Real.exp 1 * (d : ℝ) * tLU ≤ (2 : ℝ) ^ k₁) :
    ∃ h : (solutions F).Nonempty,
      ∀ (v : Fin n) (b : Bool),
        eventProb (solutionLaw F h) (fun x => x v = b) ≤
          (1 / 2 : ℝ) * Real.exp (1 / tLU) := by sorry

end CNFLearning873.Valiant
