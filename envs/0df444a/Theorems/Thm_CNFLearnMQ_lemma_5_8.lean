-- Prove2me | Theorems.Thm_CNFLearnMQ_lemma_5_8
-- name    : CNFLearnMQ.lemma_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:17:36.173271+00:00
-- url     : https://prove2.me/theorems/28fd350e-50ae-4c20-9d41-8c4d79068adb
-- title:
--   Lemma 5.8 — at most $N_{\mathrm{tot}}$ candidates are enqueued
-- statement:
--   Let $t\ge1$ be real, $k\ge100$ and $d\ge1$ integers satisfying the local lemma condition (3), $k\ge(1+1/t)\log d+2\log k+t-3\log t+5$, and let $\Phi=(V,C)$ be an $n$-variable $(k,d)$-CNF formula with $n\ge k$ (the standing assumptions of §5, p.21, and §3, p.13).
--   Fix $\varepsilon,\delta\in(0,1)$ and consider any execution of LearnCNF$(\varepsilon,\delta)$ run with sample access to $\mu_\Phi$ and membership-query access to $\Phi$. Suppose that for every rejected candidate $s=(S,\sigma_S)$ with $|S|<k$ passed to ExtendSubclause$(s,Y)$ we have $q_s\ge\eta$, and every recovered signed core $b$ considered in that call satisfies $q_s(b)\ge\widehat q_s(b)-\phi$. Then the total number of candidate subclauses enqueued into $Q$ throughout the execution is at most $N_{\mathrm{tot}}$, so the algorithm does not return $\bot$.
--
--   This is the second requirement of the extension rule, and the source of every complexity bound of the main theorem.
--
--   Differences from the source:
--   - encoding: any execution, the calls to ExtendSubclause and the total number of enqueued candidates → every outcome of positive probability of `learnCNFLogged`, its logged calls (input $s$, samples $Z_i$, recovered families) and its logged final counter (seeds included); reason: the log records exactly these quantities
--   - encoding: does not return $\bot$ → the output is not `none`; reason: $\bot$ is `none`
--   - encoding: $\mu_\Phi$, defined when $\Omega(\Phi)\ne\emptyset$ (p.13); under (3) $\Phi$ is satisfiable by Theorem 3.1 → nonemptiness of the solution set is a hypothesis `h`; reason: the published law `solutionLaw` needs the proof; under the standing assumptions it always holds, so no instance is excluded
--   - reading: LearnCore / LearnCNF with the choices the paper leaves arbitrary (deleted variable, partition, tie-breaks, queue order) → the mission's one program with fixed choices (smallest-index deletion, consecutive blocks, first minimal subset, fixed enumeration orders); reason: the algorithm is specified only up to these choices and the proofs work for every choice; one fixed implementation is the algorithm the mission formalizes, and the goal (an existence statement) is witnessed by it
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Lemma 5.8, p.28

import Mathlib
import Definitions.Def_CNFLearnMQ_Success

set_option autoImplicit false

namespace CNFLearnMQ

open CNFLearning873.Valiant

/-- Lemma 5.8, p.28 (Feng, Yu, Zhang, *Learning CNF Formulas with Uniform Random Solutions and Membership Queries*, STOC 2027 submission (manuscript sha256 519ee6d4…)). Under the standing assumptions of §5, consider any execution of LearnCNF
(any outcome of positive probability). Suppose that for every rejected candidate `s` passed to
ExtendSubclause(s, Y) we have `q_s ≥ η` and every recovered signed core `b` considered in that call
satisfies `q_s(b) ≥ q̂_s(b) − ϕ`. Then the total number of candidate subclauses enqueued into `Q`
throughout the execution is at most `N_tot`, so the algorithm does not return ⊥.

**Formalization Note** The execution is recorded by the ghost log of `learnCNFLogged`: each call to
ExtendSubclause with its input `s`, its selected samples `Zᵢ` and recovered families `R̂_{Zᵢ}`; the
considered cores are those with `B ∩ S = ∅`, `|B| + |S| ≤ k` (Algorithm 4 line 5); the logged
counter is the total number of enqueued candidates, seeds included. `µ_Φ` exists only when
`Ω(Φ) ≠ ∅`, so nonemptiness is a hypothesis (it always holds under (3), Theorem 3.1). -/
theorem lemma_5_8 {n k d : ℕ} {t ε δ : ℝ} (ht : 1 ≤ t) (hk : 100 ≤ k) (hd : 1 ≤ d) (hLLL : LLLCondition k d t) (hn : k ≤ n) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (Φ : CNF n) (hΦ : KD Φ k d) (h : (solutions Φ).Nonempty)
    (o : (Option (CNF n) × Log n) × Cost)
    (ho : o ∈ (run (solutionPMF Φ h) (memOracle Φ) (learnCNFLogged n k d t ε δ)).support)
    (hyp : ∀ call ∈ o.1.2.calls, eta n k d t ε ≤ q Φ h call.s ∧
      ∀ b ∈ considered k call.s call.Zs call.Rs,
        qhatCore (Next n k d δ) call.Zs call.Rs b - phi d k ≤ qcond Φ h call.s b) :
    o.1.2.enqueued ≤ Ntot n k d t ε ∧ o.1.1 ≠ none := by sorry

end CNFLearnMQ
