-- Prove2me | Theorems.Thm_CheungIBOL_General_theorem_1
-- name    : CheungIBOL.General.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T22:17:39.075365+00:00
-- url     : https://prove2.me/theorems/6b1408e9-3866-4b8b-bded-5be09ac2e75a
-- title:
--   Theorem 1 — general IBOL performance guarantee
-- statement:
--   Consider the general online allocation model with $n>0$ resources, positive integer capacities $b_i$, rewards $0<r_i\le1$, a finite known context set, a nonempty general measurable action space, and fixed unknown joint outcome laws on $\{0,1\}^n$. Coordinates may be correlated. Fix any oblivious context sequence of length $T>0$, any randomized history-dependent MAB oracle, and any $\epsilon\in[0,1]$. IBOL passes the current context, past observed triples and discounted rewards $r_i(1-\Psi_\epsilon(N_i^{t-1}/b_i))$ to the oracle, observes a fresh outcome for the chosen action, and consumes successful coordinates only while capacity remains. Feedback continues after depletion.
--
--   Write $\mathrm{ALG}=\sum_{t,i}r_i y_{t,i}\mathbf1\{N_i^{t-1}<b_i\}$ and
--   $$R^t(a)=\sum_i r_i(1-\Psi_\epsilon(N_i^{t-1}/b_i))p_{x_t,a,i},\qquad
--   \mathrm{Reg}_\epsilon=\mathbb E\sum_{t=1}^T\left[\sup_a R^t(a)-(1+\epsilon)R^t(a_t)\right].$$
--   The benchmark $\mathrm{OPT}$ is the supremum of $\sum_{t,i}\int r_i p_{x_t,a,i}\,ds_t(a)$ over probability measures $s_t$ satisfying $\sum_t\int p_{x_t,a,i}\,ds_t(a)\le b_i$. Define the exact positive coefficient
--   $$f_\Psi(\{b_i\},\epsilon)=\min_i\frac{1-e^{-(1+\epsilon)}}{(b_i+1+\epsilon)(1-e^{-(1+\epsilon)/b_i})}.$$
--   Then
--   $$\mathrm{OPT}\le\frac{\mathbb E[\mathrm{ALG}]}{f_\Psi(\{b_i\},\epsilon)}+\mathrm{Reg}_\epsilon.$$
--   For finite $\mathrm{OPT}$ this is precisely the source's inequality
--   $$\mathbb E[\mathrm{ALG}]\ge f_\Psi(\{b_i\},\epsilon)\bigl(\mathrm{OPT}-\mathrm{Reg}_\epsilon\bigr).$$
--   Regret is signed and may be negative; the coefficient multiplies the entire difference. No UCB guarantee, oracle maximization, coordinate independence or no-sale action is assumed. Revenue and regret are computed on the same run. This is the general framework theorem, without restricting to either application.
--
--   Differences from the source:
--   - encoding: resources and contexts are finite sets, capacities are positive integers, and rounds run from 1 to T → Fin n and Fin c, positive natural capacities, zero-based rounds, and the first T entries of a deterministic infinite context sequence; reason: reindexing and extending a finite context sequence change no instance; only past observations and the current context reach a decision
--   - encoding: randomized oracle functions with independent internal randomness and fresh chosen-pair outcome samples → probability kernels on observed histories and a recursively constructed finite-history law; reason: this is the conditional-law representation of the same randomized nonanticipating process, including correlated coordinates and post-depletion feedback
--   - reading: Algorithm 1 line 9 updates F^(t+1) from F^t whereas line 6 uses F^(t-1) → the decision in source period t uses exactly the first t-1 observations; reason: the explicit history definition on page 15 determines the consistent indexing
--   - generalization: action sums and best-action maxima over a general action set → probability-measure action integrals and bounded best-action suprema over any nonempty measurable action space; reason: every discrete source allocation is a probability measure and attained maxima equal their suprema; the statement additionally covers nonatomic allocations and unattained suprema
--   - encoding: OPT and the performance inequality are written with real-valued LP optima → OPT is the EReal supremum, with empty feasible value minus infinity, and OPT <= E[ALG]/f_Psi + Reg_epsilon; reason: for finite OPT the positive coefficient makes this exactly equation (13); infeasible LPs are defined without adding a no-consumption action or a feasibility hypothesis
-- source:
--   Cheung, Ma, Simchi-Levi and Wang, Inventory Balancing with Online Learning, arXiv:1810.05640v2 (30 August 2021), PDF/printed p. 17, Theorem 1, equations (13)–(14); model and algorithm pp. 8–16, https://arxiv.org/abs/1810.05640v2

import Definitions.Def_CheungIBOL_General_Benchmark

namespace CheungIBOL.General

theorem theorem_1 {n c : ℕ} {A : Type*} [MeasurableSpace A] [Nonempty A]
    (M : Model n c A) (O : Oracle n c A) (ε : ℝ) (hε : ε ∈ Set.Icc 0 1)
    (x : ℕ → Fin c) (T : ℕ) (hT : 0 < T) :
    optimum M x T ≤
      ((expectedRevenue M O ε x T / coefficient M.capacity ε +
        relaxedRegret M O ε x T : ℝ) : EReal) := by sorry

end CheungIBOL.General
