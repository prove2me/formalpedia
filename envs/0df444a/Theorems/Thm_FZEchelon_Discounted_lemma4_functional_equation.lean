-- Prove2me | Theorems.Thm_FZEchelon_Discounted_lemma4_functional_equation
-- name    : FZEchelon.Discounted.lemma4_functional_equation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:46:18.030965+00:00
-- url     : https://prove2.me/theorems/d296bcf3-c6ec-40a4-a1b8-72ed0a219146
-- title:
--   Lemma 4, p. 827 — $g = g^d + g^r$ satisfies the functional equation (8), with the infimum achieved by $\pi_\alpha^*$
-- statement:
--   In the two-echelon model of Federgruen and Zipkin under the standing assumptions of §1, assume $\alpha < 1$ and $\alpha^l p^r \ge (1-\alpha^l) h^d$. Let $x^{r*}$ be the critical number of the outlet problem. Let $\sigma^d$ be a measurable, nonnegative stationary order policy that is optimal for the depot problem $IH_\alpha^d$, from every depot state with $\hat y \ge 0$, among all admissible order policies. Let $g^d$ and $g^r$ be the limits of $g_n^d$ and $g_n^r$ as in Lemma 3, and $g = g^d + g^r$.
--
--   Then $g$ satisfies the infinite-horizon functional equation (8) at every physical state $(\hat y, v^d, x^r)$ ($\hat y \ge 0$, $x^r \le v^d$):
--   $$
--   g(\hat y, v^d, x^r) = \inf_{y, z}\big\{c^d(y) + D(v^d + y^L) + c^r z + R(x^r + z) + \alpha E g[(y, y^1, \dots, y^{L-1}), v^d + y^L - u, x^r + z - u]\big\},
--   $$
--   the infimum over $y \ge 0$, $z \ge 0$, $x^r + z \le v^d + y^L$. Moreover, the infimum is achieved by the action of $\pi_\alpha^*$: the order $y = \sigma^d(\hat y, v^d)$ and the shipment $z = \max\{0, \min\{x^{r*}, v^d + y^L\} - x^r\}$ are feasible and attain it.
--
--   This is the optimality equation that, with Lemma 3, lets the general theory of Bertsekas and Shreve identify $g$ as the optimal cost and $\pi_\alpha^*$ as an optimal policy (Theorem 1).
--
--   **Formalization Note.** "Satisfies (8) with the infimum achieved" is stated as: $g(s)$ is the least element of the set of values of the right-hand side over feasible actions, and the action of $\pi_\alpha^*$ is feasible and gives the value $g(s)$. The hypothesis on $\sigma^d$ is the paper's definition of $\pi_\alpha^*$ ("the policy solving $IH_\alpha^d$"). Its existence, in $(s, S)$ form, is Iglehart's result, which the paper cites; the $(s, S)$ form is not required here.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 827, eq. (8) and Lemma 4; π_α* defined on p. 825

import Mathlib
import Definitions.Def_FZEchelon_Discounted_Programs

open MeasureTheory Filter Topology

namespace FZEchelon.Discounted

/-- Lemma 4, p. 827: `g = g^d + g^r` satisfies the infinite-horizon functional equation (8) on the
physical states, and the infimum is achieved by the action of the policy `π_α*`. Here `σd` is a
measurable stationary order policy that is optimal for the depot problem `IH_α^d`. -/
theorem lemma4_functional_equation (M : Model) (hM : M.StandingAssumptions) (hα : M.α < 1)
    (hcost : (1 - M.α ^ M.l) * M.hd ≤ M.α ^ M.l * M.pr)
    (xstar : ℝ) (hx : M.IsStationaryCriticalNumber xstar)
    (σd : M.DepotState → ℝ) (hσm : Measurable σd) (hσnn : ∀ p, 0 ≤ σd p)
    (hσopt : ∀ p : M.DepotState, (∀ k, 0 ≤ p.1 k) → ∀ πd : Policy ℝ,
      (M.depotSystem xstar).Admissible πd p →
      (M.depotSystem xstar).discCost M.α M.ν ((M.depotSystem xstar).stationary σd p) p ≤
        (M.depotSystem xstar).discCost M.α M.ν πd p)
    (gdInf : M.DepotState → ℝ)
    (hgd : ∀ p : M.DepotState, (∀ k, 0 ≤ p.1 k) →
      Tendsto (fun n => M.gd xstar n p) atTop (𝓝 (gdInf p)))
    (grInf : ℝ → ℝ) (hgr : ∀ x, Tendsto (fun n => M.gr n x) atTop (𝓝 (grInf x)))
    (s : M.State) (hs : M.InDomain s) :
    IsLeast {r : ℝ | ∃ a : ℝ × ℝ, M.system.feasible s a ∧
        r = M.system.cost s a + M.α * ∫ t, (gdInf ((M.system.next s a t).1,
          (M.system.next s a t).2.1) + grInf (M.system.next s a t).2.2) ∂M.ν}
      (gdInf (s.1, s.2.1) + grInf s.2.2) ∧
    M.system.feasible s (M.piStar σd xstar s) ∧
    M.system.cost s (M.piStar σd xstar s) + M.α * ∫ t,
        (gdInf ((M.system.next s (M.piStar σd xstar s) t).1,
          (M.system.next s (M.piStar σd xstar s) t).2.1) +
         grInf (M.system.next s (M.piStar σd xstar s) t).2.2) ∂M.ν =
      gdInf (s.1, s.2.1) + grInf s.2.2 := by sorry

end FZEchelon.Discounted
