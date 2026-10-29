-- Prove2me | Theorems.Thm_BramsonQueueing_Classical_homogeneous_node_stationary
-- name    : BramsonQueueing.Classical.homogeneous_node_stationary
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:22:01.123173+00:00
-- url     : https://prove2.me/theorems/c106ac3e-cc6c-44f5-8392-73e577e0a949
-- title:
--   Theorem 2.7 — stationary law of a homogeneous Kelly node
-- statement:
--   Consider a homogeneous node of Kelly type, with finitely many classes, independent Poisson inputs of rates $\alpha_k$, common exponential service mean $m^s>0$, total service effort $\phi(n)$, and class-independent positional proportions $\beta$ and $\delta$. Retain the standing nonexplosive communicating countable-state setup. Write $\rho=m^s\sum_k\alpha_k$ and suppose $B=\sum_{n\ge0}\rho^n/\prod_{i=1}^n\phi(i)<\infty$. Then the node has stationary distribution
--   $$\pi(x)=B^{-1}\prod_{i=1}^n\frac{m^s\alpha_{x(i)}}{\phi(i)},\qquad x=(x(1),\ldots,x(n))\in S_0.$$
--   Stationarity includes normalization and invariance for every time. The formula retains arbitrary positive total service rates and arbitrary permitted positional proportions.
--
--   Differences from the source:
--   - encoding: nonnegative rates, probabilities, and possibly infinite nonnegative series → finite primitive parameters in NNReal and nonnegative sums in ENNReal; reason: infinite normalizers remain infinite; the stated finite-rate and normalization conditions exclude junk conversions
--   - encoding: a nonexplosive countable-state continuous-time Markov process → its minimal transition kernel constructed by the exponential first-jump recursion; reason: the finite-rate nonexplosive process is determined by these rates; stationarity is invariance for every nonnegative time
--   - encoding: classes numbered 1 through K and queues written as tuples → finite class types and unbounded lists, with list position i representing source position i+1; reason: finite relabelling and list representation preserve every source queue state
--   - encoding: Kelly state is a list of classes → each class is stored as the triple (k,1,1); reason: these are exactly the allowed Kelly triples, so forgetting the two unit coordinates is a bijection with S0
--   - encoding: arrival, service, and routed transition mechanisms in (2.21), (2.35), and (2.48)-(2.52) → sum the rates of mechanisms that yield the same state, and suppress invisible diagonal events; reason: multiple insertion positions or intermediate states can produce the same transition; aggregation gives the actual Markov jump rate, as in the source sums (2.26) and (2.73)
--   - encoding: station-local class labels and positional parameters on their meaningful index ranges → an ambient finite class type with a supported class subset, phi(0)=0, and total parameter arrays; symmetric beta and delta agree as total functions; reason: unused labels and array entries do not affect any transition or mass; source arrays extend with these conventions, and empty support has the unique empty-queue state
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; Theorem 2.7, printed p. 29 / PDF p. 37; Eqs. (2.19)-(2.20)

import Definitions.Def_BramsonQueueing_Classical_Stations
open scoped NNReal ENNReal

namespace BramsonQueueing.Classical

/-- Bramson, Theorem 2.7, printed p. 29 / PDF p. 37. -/
theorem homogeneous_node_stationary {C : Type*} [Fintype C] [Nonempty C]
    (D : Station C) (α : C → ℝ≥0) (hD : D.Admissible α)
    (hKelly : D.kelly = true) :
    let ρ : ℝ≥0∞ := (D.commonMean : ℝ≥0∞) * ∑ k ∈ D.classes, (α k : ℝ≥0∞)
    let B : ℝ≥0∞ := ∑' n : ℕ, ρ ^ n /
      ∏ i ∈ Finset.range n, (D.phi (i+1) : ℝ≥0∞)
    let π : D.State → ℝ≥0∞ := fun x => B⁻¹ * ∏ i : Fin x.val.length,
      (D.commonMean : ℝ≥0∞) * (α (x.val.get i).1 : ℝ≥0∞) /
        (D.phi (i.val+1) : ℝ≥0∞)
    B ≠ ⊤ → (∑' x, π x = 1) ∧ ∀ t, 0 ≤ t → ∀ y,
      ∑' x, π x * transition (D.node.queue (fun k => (α k : ℝ≥0∞))).rate t x y = π y := by sorry

end BramsonQueueing.Classical
