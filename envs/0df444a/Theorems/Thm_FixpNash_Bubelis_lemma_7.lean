-- Prove2me | Theorems.Thm_FixpNash_Bubelis_lemma_7
-- name    : FixpNash.Bubelis.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:33.358387+00:00
-- url     : https://prove2.me/theorems/75c365e0-705f-4b88-b0b2-7494baf63e3b
-- title:
--   Lemma 7, p. 25 — in every Nash equilibrium of Bubelis's gadget $G_f$ the primary player plays 0 with probability $\alpha$, the unique root of $f$ in $[0,1]$
-- statement:
--   This is Lemma 7 of Etessami and Yannakakis, a form of Bubelis's construction (Theorem 2 of Bubelis 1979).
--
--   Let $f(x) = c_0 x^m + \dots + c_m$ be a polynomial with real coefficients such that $f(0) \le 0$, $f(1) \ge 0$, and $f$ has a unique root $\alpha$ in the interval $[0,1]$. Let $G_f$ be the three-player gadget of p. 25: the primary player 1 with strategies $0, 1$ and payoff $h^f_1(s) = c_{s_2}$ if $s_1 = 1$ and $0$ if $s_1 = 0$; the auxiliary players 2, 3 with strategies $0, \dots, m$ and the $f$-independent payoffs $h_2$, $h_3$. Then:
--
--   1. every Nash equilibrium $x = (x_1, x_2, x_3)$ of $G_f$ satisfies
--   $$
--   x_1(0) = \alpha, \qquad x_1(1) = 1 - \alpha ;
--   $$
--   2. if $\alpha \ne 0$ and $\alpha \ne 1$, then $G_f$ has exactly one Nash equilibrium, and that equilibrium is fully mixed: every strategy of every player has positive probability.
--
--   The gadget lets a game "compute" a root of a polynomial in the equilibrium probability of a single player; Etessami and Yannakakis use it, with $f$ linear, as the building block of their reduction from PosSLP to the approximation of Nash equilibria of three-player games, and its uniqueness property is what makes the composed game have a unique equilibrium.
--
--   **Formalization Note** "Nash equilibrium" is the mixed Nash equilibrium of `agt_games` (no profitable unilateral mixed deviation). "The game has a unique Nash equilibrium" is read as existence and uniqueness, `∃!` over mixed profiles; the paper's proof argues uniqueness and takes existence from Nash's theorem. The unique root is a named parameter $\alpha$ with the hypothesis $0 \le \alpha \le 1$, $f(\alpha) = 0$, and $\beta = \alpha$ for every root $\beta \in [0,1]$. The coefficients are real, a generalization of the paper's rational ones; the degree of $f$ is at most $m$. For $m = 0$ the hypotheses cannot hold (a constant with a unique root in $[0,1]$ does not exist), as on the page. The last two properties stated in the lemma (the auxiliary payoffs do not depend on $f$ and lie in $\{0,1,-1\}$; the primary payoff is $c_{s_2}$ or $0$) hold by the definition of the gadget and are recorded there.
-- source:
--   Etessami & Yannakakis, On the complexity of Nash equilibria and other fixed points, author manuscript (SIAM J. Comput. 39 (2010)), Lemma 7, p. 25 (proof pp. 25–26)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_FixpNash_Bubelis_Gadget

namespace FixpNash.Bubelis

/-- **Lemma 7** (Etessami–Yannakakis, after Bubelis), p. 25. Let `f(x) = c₀ xᵐ + … + c_m` with
`f(0) ≤ 0`, `f(1) ≥ 0`, and with a unique root `α` in `[0, 1]`. Then in the gadget `G_f`:
(1) every Nash equilibrium assigns probability `α` to the strategy 0 of the primary player and
`1 − α` to its strategy 1; (2) if `α ≠ 0, 1`, the game has a unique Nash equilibrium (it exists
and is unique), and the Nash equilibrium is fully mixed. -/
theorem lemma_7 {m : ℕ} (c : Fin (m + 1) → ℝ)
    (hf0 : poly c 0 ≤ 0) (hf1 : 0 ≤ poly c 1) (α : ℝ)
    (hα : 0 ≤ α ∧ α ≤ 1 ∧ poly c α = 0 ∧
      ∀ β : ℝ, 0 ≤ β → β ≤ 1 → poly c β = 0 → β = α) :
    (∀ x : ∀ p, Strat m p → ℝ, AGT.IsMixedNash (gadget c) x →
        x .primary 0 = α ∧ x .primary 1 = 1 - α) ∧
      (α ≠ 0 → α ≠ 1 →
        (∃! x : ∀ p, Strat m p → ℝ, AGT.IsMixedNash (gadget c) x) ∧
          ∀ x : ∀ p, Strat m p → ℝ, AGT.IsMixedNash (gadget c) x → IsFullyMixed x) := by sorry

end FixpNash.Bubelis
