-- Prove2me | Theorems.Thm_BramsonQueueing_Classical_product_form_stationary_distribution
-- name    : BramsonQueueing.Classical.product_form_stationary_distribution
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:21:56.600004+00:00
-- url     : https://prove2.me/theorems/2c873eac-590d-4caf-8ac3-4f1fcf87605b
-- title:
--   Theorem 2.12 — product stationary law for mixed classical networks
-- statement:
--   Consider a finite open network with independent external Poisson input rates $\alpha_k$ and a substochastic routing matrix $P$. Define the total class rates by $\lambda=(I-P^{\mathsf T})^{-1}\alpha$. Each station $j$ is either homogeneous of Kelly type, with common positive exponential service mean $m_j^s$, or symmetric, with countably mixed Erlang service times of finite positive class means. Different stations may use different eligible types. Retain the standing nonexplosive communicating countable-state setup. With $\rho_j=\sum_{k\in C(j)}m_k\lambda_k$, suppose
--   $$B_j=\sum_{n\ge0}\frac{\rho_j^n}{\prod_{i=1}^n\phi_j(i)}<\infty\quad\text{for every }j.$$
--   Then the network has stationary distribution
--   $$\pi(x)=\prod_{j=1}^J\pi_j(x_j),$$
--   where a Kelly factor is $B_j^{-1}\prod_i m_j^s\lambda_{x_j(i)}/\phi_j(i)$, and a symmetric factor is $B_j^{-1}\prod_i p_{x_j(i)}(s(i))m_{x_j(i)}(s(i))\lambda_{x_j(i)}/\phi_j(i)$. This is normalization and invariance under the network transition semigroup, with no independence of the station trajectories asserted.
--
--   Differences from the source:
--   - encoding: nonnegative rates, probabilities, and possibly infinite nonnegative series → finite primitive parameters in NNReal and nonnegative sums in ENNReal; reason: infinite normalizers remain infinite; the stated finite-rate and normalization conditions exclude junk conversions
--   - encoding: a nonexplosive countable-state continuous-time Markov process → its minimal transition kernel constructed by the exponential first-jump recursion; reason: the finite-rate nonexplosive process is determined by these rates; stationarity is invariance for every nonnegative time
--   - encoding: classes numbered 1 through K and queues written as tuples → finite class types and unbounded lists, with list position i representing source position i+1; reason: finite relabelling and list representation preserve every source queue state
--   - encoding: Kelly state is a list of classes → each class is stored as the triple (k,1,1); reason: these are exactly the allowed Kelly triples, so forgetting the two unit coordinates is a bijection with S0
--   - encoding: arrival, service, and routed transition mechanisms in (2.21), (2.35), and (2.48)-(2.52) → sum the rates of mechanisms that yield the same state, and suppress invisible diagonal events; reason: multiple insertion positions or intermediate states can produce the same transition; aggregation gives the actual Markov jump rate, as in the source sums (2.26) and (2.73)
--   - encoding: lambda=Q alpha with Q=(I-P^T)^(-1) → lambda_l=sum_k alpha_k sum_n (P^n)_(k,l); reason: open routing makes the nonnegative fundamental series finite and equal to the source inverse
--   - encoding: station-local class labels and positional parameters on their meaningful index ranges → an ambient finite class type with a supported class subset, phi(0)=0, and total parameter arrays; symmetric beta and delta agree as total functions; reason: unused labels and array entries do not affect any transition or mass; source arrays extend with these conventions, and empty support has the unique empty-queue state
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; Theorem 2.12, printed p. 47 / PDF p. 55; Eqs. (2.20), (2.32), (2.55)-(2.56)

import Definitions.Def_BramsonQueueing_Classical_Stations
open scoped NNReal ENNReal

namespace BramsonQueueing.Classical

/-- Bramson, Theorem 2.12, printed p. 47 / PDF p. 55.
The normalizer and both station masses are unfolded for independent auditing. -/
theorem product_form_stationary_distribution {J C : Type*}
    [Fintype J] [Nonempty J] [Fintype C] [Nonempty C]
    (station : C → J) (D : J → Station C) (R : Routing C)
    (hD : MixedValid station D R) :
    let lam : C → ℝ≥0∞ := fun l =>
      ∑ k, (R.external k : ℝ≥0∞) * ∑' n, R.paths n k l
    let m : J → C → ℝ≥0∞ := fun j k =>
      if (D j).kelly then ((D j).commonMean : ℝ≥0∞)
      else ∑' s : ℕ, (s : ℝ≥0∞) * ((D j).mixture k s : ℝ≥0∞) *
        ((D j).stageMean k s : ℝ≥0∞)
    let ρ : J → ℝ≥0∞ := fun j => ∑ k ∈ (D j).classes, m j k * lam k
    let B : J → ℝ≥0∞ := fun j => ∑' n : ℕ, ρ j ^ n /
      ∏ i ∈ Finset.range n, ((D j).phi (i+1) : ℝ≥0∞)
    let π : (∀ j, (D j).State) → ℝ≥0∞ := fun x => ∏ j, (B j)⁻¹ *
      ∏ i : Fin (x j).val.length,
        let a := (x j).val.get i
        (if (D j).kelly then ((D j).commonMean : ℝ≥0∞) * lam a.1
         else ((D j).mixture a.1 a.2.1 : ℝ≥0∞) *
           ((D j).stageMean a.1 a.2.1 : ℝ≥0∞) * lam a.1) /
          ((D j).phi (i.val+1) : ℝ≥0∞)
    (∀ j, B j ≠ ⊤) →
      (∑' x, π x = 1) ∧ ∀ t, 0 ≤ t → ∀ y,
        ∑' x, π x * transition (network station (fun j => (D j).node) R).rate t x y = π y := by sorry

end BramsonQueueing.Classical
