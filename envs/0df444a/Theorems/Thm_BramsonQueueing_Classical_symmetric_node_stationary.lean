-- Prove2me | Theorems.Thm_BramsonQueueing_Classical_symmetric_node_stationary
-- name    : BramsonQueueing.Classical.symmetric_node_stationary
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:21:46.057176+00:00
-- url     : https://prove2.me/theorems/71932925-6d54-428a-a652-d5ca1674cd07
-- title:
--   Theorem 2.8 — stationary law of a symmetric Erlang-mixture node
-- statement:
--   Consider a symmetric node with independent Poisson inputs $\alpha_k$, identical positional insertion and service proportions, and countable Erlang mixtures with probabilities $p_k(s)$ and stage means $m_k(s)>0$. The class means $m_k=\sum_{s\ge1}s p_k(s)m_k(s)$ are finite. Queue states have arbitrarily many jobs, each carrying $(k,s,v)$ with $p_k(s)>0$ and $1\le v\le s$. Retain the standing nonexplosive communicating countable-state setup. Set $\rho=\sum_km_k\alpha_k$ and suppose $B=\sum_{n\ge0}\rho^n/\prod_{i=1}^n\phi(i)<\infty$. Then
--   $$\pi(x)=B^{-1}\prod_{i=1}^n\frac{p_{x(i)}(s(i))m_{x(i)}(s(i))\alpha_{x(i)}}{\phi(i)}$$
--   is a stationary distribution on $S_e$. The statement includes the refined stage information and does not bound the number of stages or the queue length.
--
--   Differences from the source:
--   - encoding: nonnegative rates, probabilities, and possibly infinite nonnegative series → finite primitive parameters in NNReal and nonnegative sums in ENNReal; reason: infinite normalizers remain infinite; the stated finite-rate and normalization conditions exclude junk conversions
--   - encoding: a nonexplosive countable-state continuous-time Markov process → its minimal transition kernel constructed by the exponential first-jump recursion; reason: the finite-rate nonexplosive process is determined by these rates; stationarity is invariance for every nonnegative time
--   - encoding: classes numbered 1 through K and queues written as tuples → finite class types and unbounded lists, with list position i representing source position i+1; reason: finite relabelling and list representation preserve every source queue state
--   - encoding: arrival, service, and routed transition mechanisms in (2.21), (2.35), and (2.48)-(2.52) → sum the rates of mechanisms that yield the same state, and suppress invisible diagonal events; reason: multiple insertion positions or intermediate states can produce the same transition; aggregation gives the actual Markov jump rate, as in the source sums (2.26) and (2.73)
--   - encoding: station-local class labels and positional parameters on their meaningful index ranges → an ambient finite class type with a supported class subset, phi(0)=0, and total parameter arrays; symmetric beta and delta agree as total functions; reason: unused labels and array entries do not affect any transition or mass; source arrays extend with these conventions, and empty support has the unique empty-queue state
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; Theorem 2.8, printed p. 34 / PDF p. 42; Eqs. (2.19), (2.30)-(2.32)

import Definitions.Def_BramsonQueueing_Classical_Stations
open scoped NNReal ENNReal

namespace BramsonQueueing.Classical

/-- Bramson, Theorem 2.8, printed p. 34 / PDF p. 42. -/
theorem symmetric_node_stationary {C : Type*} [Fintype C] [Nonempty C]
    (D : Station C) (α : C → ℝ≥0) (hD : D.Admissible α)
    (hSym : D.kelly = false) :
    let m : C → ℝ≥0∞ := fun k => ∑' s : ℕ, (s : ℝ≥0∞) *
      (D.mixture k s : ℝ≥0∞) * (D.stageMean k s : ℝ≥0∞)
    let ρ : ℝ≥0∞ := ∑ k ∈ D.classes, m k * (α k : ℝ≥0∞)
    let B : ℝ≥0∞ := ∑' n : ℕ, ρ ^ n /
      ∏ i ∈ Finset.range n, (D.phi (i+1) : ℝ≥0∞)
    let π : D.State → ℝ≥0∞ := fun x => B⁻¹ * ∏ i : Fin x.val.length,
      let a := x.val.get i
      (D.mixture a.1 a.2.1 : ℝ≥0∞) * (D.stageMean a.1 a.2.1 : ℝ≥0∞) *
        (α a.1 : ℝ≥0∞) / (D.phi (i.val+1) : ℝ≥0∞)
    B ≠ ⊤ → (∑' x, π x = 1) ∧ ∀ t, 0 ≤ t → ∀ y,
      ∑' x, π x * transition (D.node.queue (fun k => (α k : ℝ≥0∞))).rate t x y = π y := by sorry

end BramsonQueueing.Classical
