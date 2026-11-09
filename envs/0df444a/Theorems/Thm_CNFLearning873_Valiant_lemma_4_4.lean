-- Prove2me | Theorems.Thm_CNFLearning873_Valiant_lemma_4_4
-- name    : CNFLearning873.Valiant.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T05:09:29.555204+00:00
-- url     : https://prove2.me/theorems/6d3511a3-7749-480b-b330-457231f1800d
-- title:
--   Lemma 4.4 — both LargeSharing cardinality bounds
-- statement:
--   Let $F$ be any $n$-variable $(k,d)$-CNF, with integers $k\ge100$, $d\ge1$, real $t\ge1$ and $0<\varepsilon<1$, satisfying
--
--   $$k\ge(1+1/t)\log_2d+2\log_2k+t-3\log_2t+5.$$
--
--   Let $r=\lceil t\rceil$ and let $M,\lambda,\tau$ be exactly the functions of $n,k,d,t,\varepsilon$ in Equation (4), with $M=\lceil8^k\ln(d^r(2k)^{k(1+r)}n^r/\varepsilon)\rceil$, $\lambda=\varepsilon/(2td^r(2k)^{k(1+r)}n^rM^k)$ and $\tau=\lambda/(4M)$. A candidate has exactly $k$ distinct variables and is rare when its actual solution-law violation probability $q_c$ is strictly below $\tau$.
--
--   For every fixed target-clause ordering and every rare candidate $c^*$, Algorithm 1 returns a collection satisfying
--
--   $$1\le|\mathcal S(c^*)|\le\lceil t\rceil.$$
--
--   The scan is the actual LargeSharing procedure: strict overlap test, candidate signs, and deletion of selected variables from the residual. The assertion covers every ordering rather than selecting a helpful one.
--
--   Differences from the source:
--   - encoding: finite Boolean variables and forbidden assignments → Fin n and published literal-sign clauses; reason: bijective relabeling and negation of literal signs preserve every clause and assignment
--   - encoding: uniform solution distribution → an existential proof of nonempty solutions followed by the published finite uniform law; reason: satisfiability is concluded and a probability law is never placed on an empty set
--   - encoding: fixed ordering of the target clauses → every duplicate-free list enumerating F; reason: exactly the allowed arbitrary fixed orders
--   - encoding: no width-k candidates when n < k → the rare family is explicitly empty in this branch; reason: covers all small and empty instances without evaluating the parameter formulas there
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf, Lemma 4.4, printed p.15 = 1-based PDF p.15

import Definitions.Def_CNFLearning873_Valiant_LargeSharing

namespace CNFLearning873.Valiant

/-- Lemma 4.4, both bounds, p.15 = PDF p.15. The fixed clause order is arbitrary.
When n<k there are no candidates; no restriction on n is added. -/
theorem lemma_4_4 (n k d : ℕ) (t ε : ℝ) (F : CNF n)
    (hk : 100 ≤ k) (hd : 1 ≤ d) (ht : 1 ≤ t)
    (hε : 0 < ε) (hε' : ε < 1) (hF : KD F k d) (hLLL : LLLCondition k d t) :
    ∃ h : (solutions F).Nonempty,
      ∀ order : List (Clause n), order.Nodup → order.toFinset = F →
        ∀ c ∈ rare F h k d t ε,
          1 ≤ (largeSharing k t order c).card ∧
          (largeSharing k t order c).card ≤ r t := by sorry

end CNFLearning873.Valiant
