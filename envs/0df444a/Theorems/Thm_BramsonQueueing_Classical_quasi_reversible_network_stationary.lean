-- Prove2me | Theorems.Thm_BramsonQueueing_Classical_quasi_reversible_network_stationary
-- name    : BramsonQueueing.Classical.quasi_reversible_network_stationary
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:21:12.089695+00:00
-- url     : https://prove2.me/theorems/6aed1dfe-0f7b-4d89-9436-9841a9a0741d
-- title:
--   Theorem 2.11 — product law and network quasi-reversibility
-- statement:
--   Let a finite open queueing network have the transitions (2.48)-(2.52), formed from isolated nodes using independent external Poisson arrivals and Markov routing. Isolated node $j$ receives class inputs at the effective network rates $\lambda_k$. Assume the standing regularity and communication conditions, and suppose that every isolated node is quasi-reversible with stationary law $\pi_j$. Then the network has stationary distribution
--   $$\pi(x)=\prod_{j=1}^J\pi_j(x_j).$$
--   Moreover, the entire network is quasi-reversible: in stationarity its current state, future external-arrival processes, and past network-exit processes are mutually independent. This conclusion concerns external arrivals and exits, not all routed arrivals and station departures. General random routing, including returns within a station, is retained.
--
--   Differences from the source:
--   - encoding: nonnegative rates, probabilities, and possibly infinite nonnegative series → finite primitive parameters in NNReal and nonnegative sums in ENNReal; reason: infinite normalizers remain infinite; the stated finite-rate and normalization conditions exclude junk conversions
--   - encoding: a nonexplosive countable-state continuous-time Markov process → its minimal transition kernel constructed by the exponential first-jump recursion; reason: the finite-rate nonexplosive process is determined by these rates; stationarity is invariance for every nonnegative time
--   - encoding: quasi-reversibility in Eq. (2.45) and its stochastic interpretation → independence of all finite-dimensional count-process cylinders and the present state; reason: this expresses the full stochastic independence property under the specified Markov event dynamics
--   - encoding: arrival, service, and routed transition mechanisms in (2.21), (2.35), and (2.48)-(2.52) → sum the rates of mechanisms that yield the same state, and suppress invisible diagonal events; reason: multiple insertion positions or intermediate states can produce the same transition; aggregation gives the actual Markov jump rate, as in the source sums (2.26) and (2.73)
--   - generalization: station spaces S0 or Se for concreteness, with the theory stated to hold more generally → arbitrary nonempty countable station carriers with class counts and the same insertion/removal/internal mechanisms; reason: taking the ordered-queue carriers and mechanisms recovers every source instance without additional assumptions
--   - encoding: stations and classes numbered 1 through J and K, with lambda=Q alpha → nonempty finite index types and lambda_l=sum_k alpha_k sum_n (P^n)_(k,l); reason: finite relabelling preserves the source indices, and open routing makes the fundamental series finite and equal to the transposed inverse formula
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; Theorem 2.11, printed p. 45 / PDF p. 53; Eqs. (2.48)-(2.53)

import Definitions.Def_BramsonQueueing_Classical_Network
open scoped NNReal ENNReal

namespace BramsonQueueing.Classical

/-- Bramson, Theorem 2.11, printed p. 45 / PDF p. 53; both conclusions. -/
theorem quasi_reversible_network_stationary {J C : Type*}
    [Fintype J] [Nonempty J] [Fintype C] [Nonempty C]
    {S : J → Type*} [∀ j, Countable (S j)] [∀ j, Nonempty (S j)]
    (station : C → J) (N : ∀ j, Node (S j) C) (R : Routing C)
    (hN : NetworkValid station N R)
    (π : ∀ j, S j → ℝ≥0∞)
    (hQR : ∀ j, QuasiReversible ((N j).queue R.traffic) (π j)) :
    let M := network station N R
    let p : (∀ j, S j) → ℝ≥0∞ := fun x => ∏ j, π j (x j)
    ((∑' x, p x = 1) ∧ ∀ t, 0 ≤ t → ∀ y,
      ∑' x, p x * transition M.rate t x y = p y) ∧
    ∀ (past future : List (ℝ≥0 × (C → ℕ))) (z : ∀ j, S j),
      (∑' x, p x * M.traceKernel false past x z) *
        (∑' y, M.traceKernel true future z y) =
      p z * (∑' x, ∑' y, p x * M.traceKernel false past x y) *
        (∑' x, ∑' y, p x * M.traceKernel true future x y) := by sorry

end BramsonQueueing.Classical
