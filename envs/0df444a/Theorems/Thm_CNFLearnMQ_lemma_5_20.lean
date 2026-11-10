-- Prove2me | Theorems.Thm_CNFLearnMQ_lemma_5_20
-- name    : CNFLearnMQ.lemma_5_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:17:50.727893+00:00
-- url     : https://prove2.me/theorems/2341456c-e5d4-4bec-a0c0-fd15bf6075ad
-- title:
--   Lemma 5.20 — on $E_{\mathrm{seed}}$, $E_{\mathrm{grow}}$, $E_{\mathrm{prob}}$ the output is $\varepsilon$-close
-- statement:
--   Let $t\ge1$ be real, $k\ge100$ and $d\ge1$ integers satisfying the local lemma condition (3), $k\ge(1+1/t)\log d+2\log k+t-3\log t+5$, and let $\Phi=(V,C)$ be an $n$-variable $(k,d)$-CNF formula with $n\ge k$ (the standing assumptions of §5, p.21, and §3, p.13).
--   Fix $\varepsilon,\delta\in(0,1)$. Conditioned on the events $E_{\mathrm{seed}}$, $E_{\mathrm{grow}}$ and $E_{\mathrm{prob}}$, suppose LearnCNF$(\varepsilon,\delta)$ returns a formula $\widehat\Phi=(V,\widehat C)$. Then $\widehat\Phi$ is satisfiable and
--   $$d_{\mathrm{TV}}(\mu_\Phi,\mu_{\widehat\Phi})\le\varepsilon.$$
--
--   This is the approximation guarantee of the learner.
--
--   Differences from the source:
--   - encoding: conditioned on the events → on every outcome of positive probability of `learnCNFLogged` at which the three events hold on its log; reason: the conclusion is a property of the outcome; pointwise on the support is the same statement
--   - encoding: $\mu_\Phi$, defined when $\Omega(\Phi)\ne\emptyset$ (p.13); under (3) $\Phi$ is satisfiable by Theorem 3.1 → nonemptiness of the solution set is a hypothesis `h`; reason: the published law `solutionLaw` needs the proof; under the standing assumptions it always holds, so no instance is excluded
--   - reading: LearnCore / LearnCNF with the choices the paper leaves arbitrary (deleted variable, partition, tie-breaks, queue order) → the mission's one program with fixed choices (smallest-index deletion, consecutive blocks, first minimal subset, fixed enumeration orders); reason: the algorithm is specified only up to these choices and the proofs work for every choice; one fixed implementation is the algorithm the mission formalizes, and the goal (an existence statement) is witnessed by it
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Lemma 5.20, pp.34–35

import Mathlib
import Definitions.Def_CNFLearnMQ_Success

set_option autoImplicit false

namespace CNFLearnMQ

open CNFLearning873.Valiant

/-- Lemma 5.20, pp.34–35 (Feng, Yu, Zhang, *Learning CNF Formulas with Uniform Random Solutions and Membership Queries*, STOC 2027 submission (manuscript sha256 519ee6d4…)). Under the standing assumptions of §5, consider any execution of
LearnCNF (any outcome of positive probability) on which the events `E_seed`, `E_grow` and `E_prob`
hold, and suppose the algorithm returns a formula `Φ̂ = (V, Ĉ)`. Then `Φ̂` is satisfiable and
`d_TV(µ_Φ, µ_Φ̂) ≤ ε`.

**Formalization Note** "Conditioned on the events" is read pointwise: the conclusion holds on every
outcome of positive probability where the three events hold. The events are evaluated on the ghost
log of `learnCNFLogged` (the initial queue, the ExtendSubclause records, the pool). `d_TV` is the
published `HybridXorLift.tvDist` (half the `ℓ₁` distance). -/
theorem lemma_5_20 {n k d : ℕ} {t ε δ : ℝ} (ht : 1 ≤ t) (hk : 100 ≤ k) (hd : 1 ≤ d) (hLLL : LLLCondition k d t) (hn : k ≤ n) (hε0 : 0 < ε) (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (Φ : CNF n) (hΦ : KD Φ k d) (h : (solutions Φ).Nonempty)
    (o : (Option (CNF n) × Log n) × Cost)
    (ho : o ∈ (run (solutionPMF Φ h) (memOracle Φ) (learnCNFLogged n k d t ε δ)).support)
    (Φhat : CNF n) (hout : o.1.1 = some Φhat) (hseed : ESeed Φ o.1.2.seedQueue)
    (hgrow : EGrow Φ o.1.2.calls) (hprob : EProb Φ h k (eta n k d t ε) o.1.2.pool) :
    ∃ h' : (solutions Φhat).Nonempty,
      HybridXorLift.tvDist (solutionLaw Φ h).prob (solutionLaw Φhat h').prob ≤ ε := by sorry

end CNFLearnMQ
