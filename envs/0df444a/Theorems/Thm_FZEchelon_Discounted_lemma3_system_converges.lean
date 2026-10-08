-- Prove2me | Theorems.Thm_FZEchelon_Discounted_lemma3_system_converges
-- name    : FZEchelon.Discounted.lemma3_system_converges
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:46:33.109971+00:00
-- url     : https://prove2.me/theorems/6f9f40f7-8a38-4023-9ebd-999a8491ed6d
-- title:
--   Lemma 3, p. 827 — the system values $\hat g_n$ converge to $g = g^d + g^r$
-- statement:
--   In the two-echelon model of Federgruen and Zipkin under the standing assumptions of §1, assume $\alpha < 1$ and $\alpha^l p^r \ge (1-\alpha^l) h^d$. Let $x^{r*}$ and $x_n^{r*}$ be the critical numbers as above. Let $g^d$ be the limit of the depot values $g_n^d$ of program (5) on the depot states with $\hat y \ge 0$ (it exists by Iglehart, 1963b), let $g^r$ be the limit of the outlet values $g_n^r$ (property (e)), and put $g = g^d + g^r$. Then for every physical state ($\hat y \ge 0$, $x^r \le v^d$)
--   $$
--   \lim_{n \to \infty} \hat g_n(\hat y, v^d, x^r) = g^d(\hat y, v^d) + g^r(x^r) = g(\hat y, v^d, x^r).
--   $$
--
--   So the optimal finite-horizon system costs converge to the sum of the infinite-horizon limits of the stationary depot program and of the outlet program. With Lemma 4, this identifies $g$ as the infinite-horizon optimal cost.
--
--   **Formalization Note.** The limits $g^d$ and $g^r$ are cited in the paper, not proved there. They enter as functions together with the hypotheses that they are the pointwise limits; this names them and assumes nothing that is not true.
-- source:
--   Federgruen and Zipkin, Computational Issues in an Infinite-Horizon, Multiechelon Inventory Model, Oper. Res. 32(4), 1984, p. 827, Lemma 3

import Mathlib
import Definitions.Def_FZEchelon_Discounted_Programs

open MeasureTheory Filter Topology

namespace FZEchelon.Discounted

/-- Lemma 3, p. 827: with `g^d` and `g^r` the limits of `g_n^d` (program (5)) and `g_n^r`
(program (2)), the system values `ĝ_n` converge to `g = g^d + g^r` on the physical states. -/
theorem lemma3_system_converges (M : Model) (hM : M.StandingAssumptions) (hα : M.α < 1)
    (hcost : (1 - M.α ^ M.l) * M.hd ≤ M.α ^ M.l * M.pr)
    (xstar : ℝ) (hx : M.IsStationaryCriticalNumber xstar)
    (xn : ℕ → ℝ) (hxn : M.IsCriticalNumberSeq xn)
    (gdInf : M.DepotState → ℝ)
    (hgd : ∀ p : M.DepotState, (∀ k, 0 ≤ p.1 k) →
      Tendsto (fun n => M.gd xstar n p) atTop (𝓝 (gdInf p)))
    (grInf : ℝ → ℝ) (hgr : ∀ x, Tendsto (fun n => M.gr n x) atTop (𝓝 (grInf x)))
    (s : M.State) (hs : M.InDomain s) :
    Tendsto (fun n => M.ghat n s) atTop (𝓝 (gdInf (s.1, s.2.1) + grInf s.2.2)) := by sorry

end FZEchelon.Discounted
