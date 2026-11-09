-- Prove2me | Theorems.Thm_CNFLearning873_Valiant_lemma_4_3
-- name    : CNFLearning873.Valiant.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T05:08:18.685278+00:00
-- url     : https://prove2.me/theorems/3f5eb91d-470f-4a84-a8ca-30b3e1afdddc
-- title:
--   Lemma 4.3 — aggregate violation probability of all rare clauses
-- statement:
--   Let $F$ be any $n$-variable $(k,d)$-CNF, with integers $k\ge100$, $d\ge1$, real $t\ge1$ and $0<\varepsilon<1$, satisfying
--
--   $$k\ge(1+1/t)\log_2d+2\log_2k+t-3\log_2t+5.$$
--
--   Let $r=\lceil t\rceil$ and let $M,\lambda,\tau$ be exactly the functions of $n,k,d,t,\varepsilon$ in Equation (4), with $M=\lceil8^k\ln(d^r(2k)^{k(1+r)}n^r/\varepsilon)\rceil$, $\lambda=\varepsilon/(2td^r(2k)^{k(1+r)}n^rM^k)$ and $\tau=\lambda/(4M)$. A candidate has exactly $k$ distinct variables and is rare when its actual solution-law violation probability $q_c$ is strictly below $\tau$.
--
--   The target is satisfiable and
--
--   $$\Pr_{X\sim\mu_F}\!\left(\bigcup_{c^*\in\mathcal C^*_{<\tau}}\{X_{\operatorname{vbl}(c^*)}=\sigma_{c^*}\}\right)\le\varepsilon.$$
--
--   The union includes every rare candidate, including valid candidates of violation probability zero. This aggregate bound is the structural result needed for the learner's total variation guarantee.
--
--   Differences from the source:
--   - encoding: finite Boolean variables and forbidden assignments → Fin n and published literal-sign clauses; reason: bijective relabeling and negation of literal signs preserve every clause and assignment
--   - encoding: uniform solution distribution → an existential proof of nonempty solutions followed by the published finite uniform law; reason: satisfiability is concluded and a probability law is never placed on an empty set
--   - encoding: union of rare-clause violation events → the predicate there exists a rare clause violated by X; reason: same finite union
--   - encoding: no width-k candidates when n < k → the rare family is explicitly empty in this branch; reason: the union is empty and the conclusion still covers these inputs
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf, Lemma 4.3, printed p.14 = 1-based PDF p.14

import Definitions.Def_CNFLearning873_Valiant_Thresholds

namespace CNFLearning873.Valiant

/-- Lemma 4.3, p.14 = PDF p.14. All rare clauses, including zero-probability
valid candidates. All thresholds are computed by Equation (4). -/
theorem lemma_4_3 (n k d : ℕ) (t ε : ℝ) (F : CNF n)
    (hk : 100 ≤ k) (hd : 1 ≤ d) (ht : 1 ≤ t)
    (hε : 0 < ε) (hε' : ε < 1) (hF : KD F k d) (hLLL : LLLCondition k d t) :
    ∃ h : (solutions F).Nonempty,
      eventProb (solutionLaw F h)
        (fun x => ∃ c ∈ rare F h k d t ε, Violates c x) ≤ ε := by sorry

end CNFLearning873.Valiant
