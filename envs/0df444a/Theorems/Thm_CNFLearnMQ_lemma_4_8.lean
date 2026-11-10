-- Prove2me | Theorems.Thm_CNFLearnMQ_lemma_4_8
-- name    : CNFLearnMQ.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:15:34.428108+00:00
-- url     : https://prove2.me/theorems/3093f767-553c-4e0d-a80b-a8034810e421
-- title:
--   Lemma 4.8 — each LearnCore iteration finds a new core with probability $\ge 1/(2(16dk)^k)$
-- statement:
--   Let $\Phi=(V,C)$ be a CNF formula on $n$ variables with $m=|C|\ge1$ nonempty clauses, each of width at most $k$, in which every variable occurs in at most $d$ clauses (the standing assumptions of §4, p.15).
--   Let $X$ be a solution and let $\mathcal F$ be the list of cores discovered before a main-loop iteration of LearnCore. If some core of $X$ is not in $\mathcal F$, then the next iteration returns a core of $X$ that is not in $\mathcal F$ with probability at least
--   $$\frac{1}{2(16dk)^k}.$$
--
--   Together with Lemma 4.7 this drives the success probability of Theorem 4.5: after $T$ consecutive unsuccessful iterations an undiscovered core is unlikely to remain.
--
--   Differences from the source:
--   - generalization: any history $H$ of positive probability before an iteration, and the conditional probability given $H$ → any list $\mathcal F$ of cores of $X$, and the probability under the run of one iteration started from $\mathcal F$; reason: the iteration's coins are fresh, so given $H$ the iteration is distributed as `learnCoreIter` from $H$'s discovered list, which is a list of cores (Lemma 4.7)
--   - encoding: the next iteration finds a new core → the iteration returns `some R` with $R\in\mathcal R_X$ and $R\notin\mathcal F$; reason: this is what finding a new core means; the iteration draws no samples, so the sample law is arbitrary
--   - reading: LearnCore / LearnCNF with the choices the paper leaves arbitrary (deleted variable, partition, tie-breaks, queue order) → the mission's one program with fixed choices (smallest-index deletion, consecutive blocks, first minimal subset, fixed enumeration orders); reason: the algorithm is specified only up to these choices and the proofs work for every choice; one fixed implementation is the algorithm the mission formalizes, and the goal (an existence statement) is witnessed by it
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Lemma 4.8, p.19

import Mathlib
import Definitions.Def_CNFLearnMQ_learnCore
import Definitions.Def_CNFLearnMQ_memOracle

set_option autoImplicit false

namespace CNFLearnMQ

open CNFLearning873.Valiant

/-- Lemma 4.8, p.19 (Feng, Yu, Zhang, *Learning CNF Formulas with Uniform Random Solutions and Membership Queries*, STOC 2027 submission (manuscript sha256 519ee6d4…)). Under the standing assumptions of §4 (p.15), let `X` be a solution and
let `found` be the cores discovered before a main-loop iteration of LearnCore. If some core of `X`
is not in `found`, the next iteration finds a new core (a core of `X` not in `found`) with
probability at least `1/(2(16dk)^k)`.

**Formalization Note** The paper conditions on a history of positive probability; the iteration's
coins are fresh, so the conditional law of the iteration given the history is the law of
`learnCoreIter` started from the history's discovered list. The statement is made for every list of
cores of `X` (every reachable history has this form, Lemma 4.7). The iteration draws no samples, so
the sample law `μ` is arbitrary. -/
theorem lemma_4_8 {n k d : ℕ} (Φ : CNF n) (hm : 1 ≤ Φ.card)
    (hw : ∀ c ∈ Φ, 1 ≤ width c ∧ width c ≤ k) (hdeg : DegreeBound Φ d)
    (X : Assignment n) (hX : X ∈ solutions Φ) (found : List (Finset (Fin n)))
    (hfound : ∀ R ∈ found, R ∈ cores Φ X) (hund : ∃ R ∈ cores Φ X, R ∉ found)
    (μ : PMF (Assignment n)) :
    ENNReal.ofReal (1 / (2 * (16 * (d : ℝ) * k) ^ k)) ≤
      prob (run μ (memOracle Φ) (learnCoreIter n k d X found))
        (fun o => ∃ R, o.1 = some R ∧ R ∈ cores Φ X ∧ R ∉ found) := by sorry

end CNFLearnMQ
