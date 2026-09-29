-- Prove2me | Theorems.Thm_BanditAlgorithm_arena_lower_bound_parameter_choice
-- name    : BanditAlgorithm.arena_lower_bound_parameter_choice
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-04T23:09:27.43181+00:00
-- url     : https://prove2.me/theorems/c1ab9fe1-8821-45e0-94e1-aad0fa7cdde1
-- title:
--   Simultaneous parameter tuning for the $\sqrt{DSAn}$ MDP lower bound
-- statement:
--   **The parameter tuning of the $\Omega(\sqrt{DSAn})$ MDP lower bound**, isolated as a self-contained statement about real numbers.
--
--   The lower-bound construction has many free parameters: the restart probability $\delta$, the planted advantage $\Delta$, a truncation level $N$, a scale $D_{sc}$, and constants $c_1, c_2, c_3, \varepsilon$. The change-of-measure step imposes a long list of compatibility constraints among them, and the point of this lemma is that the constraints are simultaneously satisfiable, with enough room left over to reach the target rate.
--
--   Given the structural data of the construction — $S \ge 3$ states, $A \ge 2$ actions, a tree of depth $d$ with $A^d < A(S-2)$, and $L \ge 1$ leaves with $S - 2 \le 3L + 1$, so that the family has $k = LA$ members — and given a horizon with $n \ge DSA$ and a diameter budget $D \ge 20(1 + \log_A S)$, one may choose the parameters so that *every* constraint holds and, simultaneously,
--   $$\frac{1}{12500}\sqrt{DSAn} \;\le\; \frac{c_1^2c_3}{16}\sqrt{\frac{D_{sc}kn}{2c_2}} - \frac{1/2+\Delta}{\delta}, \qquad 4\left(\tfrac1\delta + d + 1\right) \le D.$$
--
--   The second inequality is the diameter budget: an episode costs $d$ steps of descent, one gamble and a $\mathrm{Geom}(\delta)$ sojourn of mean $1/\delta$, and the diameter is four such episodes. The first says the main term of Step 2 survives after subtracting the transient cost of one episode.
--
--   A witnessing choice is $\delta = 1/\rho$ with $\rho = \max\{1, \min(\lfloor D/4\rfloor - d - 1,\ \lfloor kn/6000\rfloor + 1)\}$, then $\lambda = \rho + d + 1$, $N = \lfloor (n - d - 12\rho)/(2\rho + d)\rfloor$, $D_{sc} = n/N$, $c_1 = 63/64$, $\varepsilon = 1/64$, $c_2 = (n+\rho)/(\lambda N)$ and $c_3 = \rho N/n$.
--
--   Two features of this choice deserve comment. First, $\rho$ must be **capped** at $\Theta(kn)$ and not simply set to the largest value the diameter allows: the net bound $c\sqrt{\rho n} - \rho/2$ is unimodal in $\rho$, so saturating the diameter budget overshoots the optimum and can make the bound vacuous. Second, $D_{sc}$ is a free *scale* and not the diameter itself; taking $D_{sc} = n/N$ makes the truncation, calibration and upper-bound constraints hold with equality, which is what leaves the whole slack available for the rate.
-- source:
--   ORIGIN: Thomas Jaksch, Ronald Ortner, Peter Auer, 'Near-optimal Regret Bounds for Reinforcement Learning', JMLR 11 (2010) 1563-1600, Theorem 5 (p. 1567) and its proof in Section 6 'The Lower Bound', pp. 1582-1586. JAO prove: for S, A >= 10, D >= 20 log_A S and T >= DSA there is an MDP with S states, A actions and diameter D forcing expected regret >= 0.015 sqrt(DSAT). EXPOSITION FOLLOWED HERE: Lattimore-Szepesvari, Bandit Algorithms, Cambridge 2020, Theorem 38.7 (p. 529) and Section 38.7 (pp. 529-534), which restates the result for S >= 3, A >= 2, D >= 6 + 2 log_A S. DEVIATION: L&S build 'a tree of minimum depth' (p. 529); this node instead places every leaf at the SAME depth. With leaves at two depths an episode through a shallow leaf is one round shorter, worth about delta/2 of gain, while the planted advantage is only Delta = Theta(sqrt(kD/n)), so for large n the optimal gain is attained at a leaf carrying no advantage and L&S Claim 38.11 fails. JAO avoid this because their tree only connects the s-circle states and is collapsed in the analysis. This node supplies the parameter tuning (JAO choose epsilon = (1/5) sqrt(k A' D'/T) with delta = 4/D, p. 1585; L&S tune Delta and delta in Section 38.7).

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped NNReal

theorem BanditAlgorithm.arena_lower_bound_parameter_choice
    (S A n L d k : ℕ) (D : ℝ)
    (hS : 3 ≤ S) (hA : 2 ≤ A)
    (hD : 20 * (1 + Real.log S / Real.log A) ≤ D)
    (hn : D * S * A ≤ (n : ℝ))
    (hdep : A ^ d < A * (S - 2)) (hL : S - 2 ≤ 3 * L + 1) (hL1 : 1 ≤ L)
    (hk : k = L * A) :
    ∃ (δ Δ : ℝ≥0) (N : ℕ) (ε c₁ c₂ c₃ Dsc : ℝ),
      δ ≤ 1 ∧ (0 : ℝ) < δ ∧ Δ ≤ 1 / 4 ∧ Δ ≤ 1 / 2 ∧
      2 ≤ k ∧ 0 < n ∧ 0 < N ∧ 0 < Dsc ∧ 0 < c₁ ∧ 0 < c₂ ∧ 0 < c₃ ∧
      (N : ℝ) ≤ n / Dsc ∧ c₃ * Dsc ≤ 1 / (δ : ℝ) ∧
      c₁ * n / Dsc ≤ (1 - ε) * N ∧
      ((n : ℝ) + 1 / (δ : ℝ)) / (1 / (δ : ℝ) + d + 1) ≤ c₂ * n / Dsc ∧
      d + N * (d + 2) ≤ n ∧
      (2 : ℝ) ^ N ≤ ε * (1 + (δ : ℝ)) ^ N * (1 + (δ : ℝ) / 2) ^ (n - d - N * (d + 2)) ∧
      (Δ : ℝ) = c₁ * ((k : ℝ) - 1) / 2 * Real.sqrt (Dsc / (2 * c₂ * n * k)) ∧
      4 * (1 / (δ : ℝ) + d + 1) ≤ D ∧
      (1 / 12500) * Real.sqrt (D * S * A * n)
        ≤ c₁ ^ 2 * c₃ / 16 * Real.sqrt (Dsc * k * n / (2 * c₂))
            - (1 / 2 + (Δ : ℝ)) / (δ : ℝ) := by
  sorry
