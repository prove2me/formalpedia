-- Prove2me | Theorems.Thm_CNFLearning873_Valiant_lemma_4_5
-- name    : CNFLearning873.Valiant.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T05:11:02.837207+00:00
-- url     : https://prove2.me/theorems/e882457c-5eb2-42cf-95d4-2bc31dac4e6d
-- title:
--   Lemma 4.5 — representative bound throughout refinement
-- statement:
--   Let $F$ be any $n$-variable $(k,d)$-CNF, with integers $k\ge100$, $d\ge1$, real $t\ge1$ and $0<\varepsilon<1$, satisfying
--
--   $$k\ge(1+1/t)\log_2d+2\log_2k+t-3\log_2t+5.$$
--
--   Let $r=\lceil t\rceil$ and let $M,\lambda,\tau$ be exactly the functions of $n,k,d,t,\varepsilon$ in Equation (4), with $M=\lceil8^k\ln(d^r(2k)^{k(1+r)}n^r/\varepsilon)\rceil$, $\lambda=\varepsilon/(2td^r(2k)^{k(1+r)}n^rM^k)$ and $\tau=\lambda/(4M)$. A candidate has exactly $k$ distinct variables and is rare when its actual solution-law violation probability $q_c$ is strictly below $\tau$.
--
--   Fix arbitrary orders of variables and target clauses. For each attained LargeSharing output $\mathcal S$, start with its merged subclause and the entire rare-candidate group assigned to it. The finite refinement construction is well-defined and preserves its subclause and partition invariants. For every permitted tree and every internal node $s'$, the selected representatives satisfy
--
--   $$|\widetilde{\mathcal C}^{*}_{s'}|\le M.$$
--
--   Representatives are maximal by inclusion among pairwise disjoint residual supports. The bound covers every such choice throughout the recursively generated tree. The stopping boundary is $q_{s'}\le\lambda$ and the internal boundary is $q_{s'}>\lambda$.
--
--   Differences from the source:
--   - encoding: finite Boolean variables and forbidden assignments → Fin n and published literal-sign clauses; reason: bijective relabeling and negation of literal signs preserve every clause and assignment
--   - encoding: uniform solution distribution → an existential proof of nonempty solutions followed by the published finite uniform law; reason: satisfiability is concluded and a probability law is never placed on an empty set
--   - encoding: the refinement tree constructed above Lemma 4.5 → a finite derivation of the exact construction plus existence and the stated construction invariants; reason: represents the construction and its surrounding assertions from pp.16–17 without assuming its bounds
--   - encoding: a group indexed by an attained output S → each rare candidate indexes its full output group; reason: every attained output has such a candidate and no group is omitted
--   - encoding: fixed orders and arbitrary maximal choices → all permutation lists and all derivations permitted by inclusion maximality; reason: no favorable order or maximal subfamily is selected
--   - encoding: no width-k candidates when n < k → the rare family is explicitly empty in this branch; reason: small inputs produce no refinement groups
-- source:
--   Weiming Feng, Yixiao Yu, Yiyao Zhang, STOC 2027 submission #873 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/873.pdf, Lemma 4.5, printed p.17 = 1-based PDF p.17; construction pp.16–17

import Definitions.Def_CNFLearning873_Valiant_Refinement

namespace CNFLearning873.Valiant

/-- Lemma 4.5, p.17 = PDF p.17, on the actual grouped refinement construction.
Existence and invariants make explicit that its representation is well-defined.
The size assertion covers every permitted maximal choice at every internal node. -/
theorem lemma_4_5 (n k d : ℕ) (t ε : ℝ) (F : CNF n)
    (hk : 100 ≤ k) (hd : 1 ≤ d) (ht : 1 ≤ t)
    (hε : 0 < ε) (hε' : ε < 1) (hF : KD F k d) (hLLL : LLLCondition k d t) :
    ∃ h : (solutions F).Nonempty,
      ∀ order : List (Clause n), order.Nodup → order.toFinset = F →
        ∀ vorder : List (Fin n), vorder.Nodup → vorder.toFinset = Finset.univ →
          ∀ c ∈ rare F h k d t ε,
            let S := largeSharing k t order c
            let s := mergeParts S
            let A := sharingGroup F h k d t ε order S
            (∃ T, Builds F h k (parameterLambda n k d t ε) vorder s A T) ∧
            ∀ T, Builds F h k (parameterLambda n k d t ε) vorder s A T →
              TreeWellFormed T ∧
              ∀ R ∈ internalFamilies T, R.card ≤ parameterM n k d t ε := by sorry

end CNFLearning873.Valiant
