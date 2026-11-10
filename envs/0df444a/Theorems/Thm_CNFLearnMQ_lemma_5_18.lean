-- Prove2me | Theorems.Thm_CNFLearnMQ_lemma_5_18
-- name    : CNFLearnMQ.lemma_5_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:17:26.01992+00:00
-- url     : https://prove2.me/theorems/9a5590b6-3cb5-4a53-b33b-b221249626fb
-- title:
--   Lemma 5.18 — $E_{\mathrm{prob}}$ holds with probability $\ge 1-\delta/6$
-- statement:
--   Let $t\ge1$ be real, $k\ge100$ and $d\ge1$ integers satisfying the local lemma condition (3), $k\ge(1+1/t)\log d+2\log k+t-3\log t+5$, and let $\Phi=(V,C)$ be an $n$-variable $(k,d)$-CNF formula with $n\ge k$ (the standing assumptions of §5, p.21, and §3, p.13).
--   Fix $\varepsilon,\delta\in(0,1)$ and let $Y=(Y_1,\dots,Y_{N_{\mathrm{pool}}})$ be independent samples from $\mu_\Phi$. The event $E_{\mathrm{prob}}$ — for every subclause $s$ of width at most $k$, if its empirical violation frequency satisfies $\widehat q_s\le2\eta$ then $q_s\le3\eta$, whereas $\widehat q_s>2\eta$ implies $q_s\ge\eta$ — occurs with probability at least
--   $$1-\delta/6.$$
--
--   On this event every accepted candidate excludes at most a $3\eta$ fraction of the solutions, and every extended candidate has $q_s\ge\eta$.
--
--   Differences from the source:
--   - encoding: the pool of $N_{\mathrm{pool}}$ independent samples → the law `iidList` of $N_{\mathrm{pool}}$ independent draws; reason: same distribution
--   - encoding: $\mu_\Phi$, defined when $\Omega(\Phi)\ne\emptyset$ (p.13); under (3) $\Phi$ is satisfiable by Theorem 3.1 → nonemptiness of the solution set is a hypothesis `h`; reason: the published law `solutionLaw` needs the proof; under the standing assumptions it always holds, so no instance is excluded
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Lemma 5.18, p.34 (Definition 5.16 item 3, p.33)

import Mathlib
import Definitions.Def_CNFLearnMQ_Success

set_option autoImplicit false

namespace CNFLearnMQ

open CNFLearning873.Valiant

/-- Lemma 5.18, p.34 (Feng, Yu, Zhang, *Learning CNF Formulas with Uniform Random Solutions and Membership Queries*, STOC 2027 submission (manuscript sha256 519ee6d4…)). Under the standing assumptions of §5, the event `E_prob`
(Definition 5.16 item 3, p.33: for every subclause `s` of width at most `k`, `q̂_s ≤ 2η` implies
`q_s ≤ 3η` and `q̂_s > 2η` implies `q_s ≥ η`) on the pool `Y = (Y_1, …, Y_{N_pool})` of independent
samples from `µ_Φ` occurs with probability at least `1 − δ/6`.

**Formalization Note** `η` and `N_pool` are the parameters (7) and (8). `µ_Φ` exists only when
`Ω(Φ) ≠ ∅`, so nonemptiness is a hypothesis (it always holds under (3), Theorem 3.1). -/
theorem lemma_5_18 {n k d : ℕ} {t ε δ : ℝ} (ht : 1 ≤ t) (hk : 100 ≤ k) (hd : 1 ≤ d) (hLLL : LLLCondition k d t) (hn : k ≤ n) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (Φ : CNF n) (hΦ : KD Φ k d) (h : (solutions Φ).Nonempty) :
    ENNReal.ofReal (1 - δ / 6) ≤
      prob (iidList (solutionPMF Φ h) (Npool n k d t ε δ)) (EProb Φ h k (eta n k d t ε)) := by sorry

end CNFLearnMQ
