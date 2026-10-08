-- Prove2me | Theorems.Thm_FZEchelon_Discounted_lemma2_depot_uniform
-- name    : FZEchelon.Discounted.lemma2_depot_uniform
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:46:02.98706+00:00
-- url     : https://prove2.me/theorems/1ef15ed8-b472-41fa-881b-c09243a9dfa8
-- title:
--   Lemma 2, p. 826 — $\hat g_n^d - g_n^d$ is eventually bounded and converges uniformly to $0$ on $\{\hat y \ge 0\}$
-- statement:
--   In the two-echelon model of Federgruen and Zipkin under the standing assumptions of §1, assume $\alpha < 1$ and $\alpha^l p^r \ge (1-\alpha^l) h^d$, and assume, as on p. 821, that the cost factors preclude it being optimal never to order: from some depot state with $\hat y \ge 0$, some admissible order policy has a strictly smaller expected discounted depot cost $B^{d\alpha}$ than the policy that never orders. Let $x^{r*}$ and $x_n^{r*}$ be the critical numbers as above, $\hat g_n^d$ the values of the depot program (3) with the penalties $\hat P_n$, and $g_n^d$ those of the depot program (5) with the stationary penalty $P$. Put
--   $$
--   \delta_n = \sup\{|\hat g_n^d(\hat y, v^d) - g_n^d(\hat y, v^d)| : \hat y \ge 0,\ v^d \in \mathbb R\}.
--   $$
--   Then $\delta_n < \infty$ for all sufficiently large $n$, and
--   $$
--   \delta_n \to 0 \qquad (n \to \infty),
--   $$
--   i.e. $\hat g_n^d - g_n^d \to 0$ uniformly on the depot states with nonnegative outstanding orders.
--
--   Together with Lemma 1, this shows that the nonstationarity of program (3) washes out: in the limit the depot can be analyzed with the stationary penalty $P$.
--
--   **Formalization Note.** The domain is the one in the paper's proof ($\hat y \ge 0$, $v^d \in \mathbb R$). The paper says the differences are bounded, but for $L \ge 1$ and $\alpha > 0$ one has $\hat g_1^d - g_1^d = (\hat P_1 - P)(v^d + y^L)$, which is unbounded in $v^d$ (see Lemma 1). The paper's recursion $\delta_n \le \gamma_n + \alpha\delta_{n-1}$ starts from $\gamma_1 = \infty$. Boundedness is therefore stated for all large $n$, which uniform convergence already implies; the uniform convergence is as printed. The standing assumption of p. 821 that never ordering is not optimal is the hypothesis `hord`. It is stated for the depot problem $IH_\alpha^d$, to which the system problem decomposes. Without it the statement is false. Take $l = 0$, $L = 1$, $\alpha = 1/2$, $c^r = 4$, $h^d = 10$, $p^r = 1$: then $\alpha^l p^r \ge (1-\alpha^l)h^d$ holds, but $D + P$ and every $D + \hat P_n$ are nondecreasing, so neither depot program ever orders. Then $\hat g_n^d - g_n^d$ contains the term $\alpha^{n-1} E(\hat P_1 - P)(\cdot)$ evaluated at a position that falls with $v^d$, and this term is unbounded in $v^d$ for every $n$.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 826, Lemma 2 (domain of δ_n from its proof, p. 826)

import Mathlib
import Definitions.Def_FZEchelon_Discounted_Programs

open MeasureTheory Filter Topology

namespace FZEchelon.Discounted

/-- Lemma 2, p. 826: the differences `ĝ_n^d − g_n^d` are (eventually) bounded and converge uniformly
to the zero function on the depot states `ŷ ≥ 0`, `v^d ∈ ℝ`. `hord` is the standing assumption of
p. 821 that the cost factors "preclude it being optimal never to order": the never-order policy is
not optimal for the depot problem `IH_α^d`. -/
theorem lemma2_depot_uniform (M : Model) (hM : M.StandingAssumptions) (hα : M.α < 1)
    (hcost : (1 - M.α ^ M.l) * M.hd ≤ M.α ^ M.l * M.pr)
    (xstar : ℝ) (hx : M.IsStationaryCriticalNumber xstar)
    (xn : ℕ → ℝ) (hxn : M.IsCriticalNumberSeq xn)
    (hord : ∃ p : M.DepotState, (∀ k, 0 ≤ p.1 k) ∧ ∃ πd : Policy ℝ,
      (M.depotSystem xstar).Admissible πd p ∧
      (M.depotSystem xstar).discCost M.α M.ν πd p <
        (M.depotSystem xstar).discCost M.α M.ν ((M.depotSystem xstar).stationary (fun _ => 0) p) p) :
    (∃ N : ℕ, ∀ n, N ≤ n → ∃ C : ℝ, ∀ p : M.DepotState, (∀ k, 0 ≤ p.1 k) →
        |M.ghatd xn n p - M.gd xstar n p| ≤ C) ∧
      TendstoUniformlyOn (fun n p => M.ghatd xn n p - M.gd xstar n p) (fun _ => 0) atTop
        {p : M.DepotState | ∀ k, 0 ≤ p.1 k} := by sorry

end FZEchelon.Discounted
