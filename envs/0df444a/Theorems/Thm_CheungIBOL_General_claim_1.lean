-- Prove2me | Theorems.Thm_CheungIBOL_General_claim_1
-- name    : CheungIBOL.General.claim_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T22:17:01.205106+00:00
-- url     : https://prove2.me/theorems/0664aee6-b042-41fe-97f6-b10c7a2be281
-- title:
--   Claim 1 — dual feasibility and expected dual bound
-- statement:
--   Fix any admissible model with positive resource capacities, rewards in $(0,1]$, finitely many contexts, and a nonempty general measurable action space. Let $T>0$, fix an oblivious context sequence and any history-dependent randomized oracle, and let $\epsilon\ge0$ (with no upper bound). Run IBOL with $\Psi_\epsilon(u)=(e^{(1+\epsilon)u}-1)/(e^{1+\epsilon}-1)$.
--
--   For every length-$T$ observed history, compute its saturated inventory path from zero and set $\Lambda_i=r_i\Psi_\epsilon(N_i^T/b_i)$ and $\Gamma_t=\sup_a\sum_i p_{x_t,a,i}r_i(1-\Psi_\epsilon(N_i^{t-1}/b_i))$. Then both conclusions hold:
--
--   1. The certificate is feasible for the literal printed Dual: $\Gamma_t\ge\sum_i p_{x_t,a,i}(r_i-\Lambda_i)$ and $p_{x_t,a,i}\Lambda_i\ge0$ for every action, period and resource.
--   2. The actual LP benchmark satisfies
--   $$\mathrm{OPT}\le\mathbb E\left[\sum_{t=1}^T\Gamma_t+\sum_i b_i\Lambda_i\right].$$
--
--   The expectation is over the constructed IBOL run, including both action and outcome randomness. Feasibility of the certificate is a conclusion, not an assumption. This is the source's link between the LP benchmark and the random certificate.
--
--   Differences from the source:
--   - encoding: resources and contexts are finite sets, capacities are positive integers, and rounds run from 1 to T → Fin n and Fin c, positive natural capacities, zero-based rounds, and the first T entries of a deterministic infinite context sequence; reason: reindexing and extending a finite context sequence change no instance; only past observations and the current context reach a decision
--   - encoding: randomized oracle functions with independent internal randomness and fresh chosen-pair outcome samples → probability kernels on observed histories and a recursively constructed finite-history law; reason: this is the conditional-law representation of the same randomized nonanticipating process, including correlated coordinates and post-depletion feedback
--   - reading: Algorithm 1 line 9 updates F^(t+1) from F^t whereas line 6 uses F^(t-1) → the decision in source period t uses exactly the first t-1 observations; reason: the explicit history definition on page 15 determines the consistent indexing
--   - generalization: action sums and best-action maxima over a general action set → probability-measure action integrals and bounded best-action suprema over any nonempty measurable action space; reason: every discrete source allocation is a probability measure and attained maxima equal their suprema; the statement additionally covers nonatomic allocations and unattained suprema
--   - encoding: OPT is bounded by the expected real dual objective → the EReal LP supremum is bounded by the real expectation embedded in EReal; reason: finite feasible source optima are unchanged, and an empty feasible set has value minus infinity
--   - generalization: dual feasibility for each realization of the algorithm inventory path → dual feasibility for every length-T Boolean observation history, even one of probability zero; reason: each history generates the same saturated inventory recursion from zero, and every actual realization is included
-- source:
--   Cheung, Ma, Simchi-Levi and Wang, Inventory Balancing with Online Learning, arXiv:1810.05640v2 (30 August 2021), Appendix A.2, PDF/printed pp. 39–40, Claim 1 and equations (31)–(35), https://arxiv.org/abs/1810.05640v2

import Definitions.Def_CheungIBOL_General_Benchmark

open MeasureTheory

namespace CheungIBOL.General

theorem claim_1 {n c : ℕ} {A : Type*} [MeasurableSpace A] [Nonempty A]
    (M : Model n c A) (O : Oracle n c A) (ε : ℝ) (hε : 0 ≤ ε)
    (x : ℕ → Fin c) (T : ℕ) (hT : 0 < T) :
    (∀ h : History n c A, h.length = T →
      DualFeasible M x T (certificateLambda M ε h) (certificateGamma M ε x T h)) ∧
    optimum M x T ≤
      ((∫ h, certificateObjective M ε x T h ∂runLaw M O ε x T : ℝ) : EReal) := by sorry

end CheungIBOL.General
