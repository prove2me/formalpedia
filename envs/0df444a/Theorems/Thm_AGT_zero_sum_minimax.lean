-- Prove2me | Theorems.Thm_AGT_zero_sum_minimax
-- name    : AGT.zero_sum_minimax
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T23:15:02.043276+00:00
-- url     : https://prove2.me/theorems/7185da9a-2cdf-430e-a89b-cfaf27f4eefb
-- title:
--   Zero-sum games: optimal strategies form a Nash equilibrium
-- statement:
--   Every finite two-person zero-sum game has optimal mixed strategies, and they form a Nash equilibrium of the game. Let $A$ be a real $(m{+}1) \times (n{+}1)$ payoff matrix: the row player picks a probability vector $p$ over rows, the column player a probability vector $q$ over columns, and the column player pays the row player $p^{\mathsf T} A q$ in expectation. Then there exist probability vectors $p^\ast, q^\ast$ such that
--
--   1. for every probability vector $p$ over rows, $\;p^{\mathsf T} A q^\ast \le (p^\ast)^{\mathsf T} A q^\ast$ — against $q^\ast$, the row player cannot do better than $p^\ast$;
--   2. for every probability vector $q$ over columns, $\;(p^\ast)^{\mathsf T} A q^\ast \le (p^\ast)^{\mathsf T} A q$ — against $p^\ast$, the column player cannot pay less than under $q^\ast$;
--   3. the pair $(p^\ast, q^\ast)$ is a **mixed Nash equilibrium** (in the sense of the `IsMixedNash` predicate of this mission) of the explicit two-player game in which the row player's payoff on the pure profile $(x,y)$ is $A_{xy}$ and the column player's is $-A_{xy}$ — the payoffs summing to zero is precisely the zero-sum condition, here formal rather than implicit in the shape of the statement.
--
--   Consequently the game has a value and $\max_p \min_q p^{\mathsf T} A q = \min_q \max_p p^{\mathsf T} A q$ (von Neumann, 1928). This is Theorem 1.11 of *Algorithmic Game Theory*, which obtains the pair as the optimal solutions of a dual pair of linear programs.
--
--   *A note on the rendering.* The book's statement — "optimum solutions of the linear programs give distributions that form a Nash equilibrium of the two-person zero-sum game" — is rendered without committing to an LP encoding: conclusions 1–2 are the saddle point that LP optimality amounts to, and conclusion 3 is the Nash-equilibrium clause, stated against the series' game vocabulary so that "zero-sum game" has a formal referent. The dimensions $m{+}1$, $n{+}1$ keep both strategy sets nonempty; over an empty strategy set there are no probability vectors and no equilibrium.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Section 1.4.2, Theorem 1.11, pp. 16-18

import Definitions.Def_agt_games
import Mathlib.Analysis.Convex.StdSimplex

namespace AGT

/-- **Theorem 1.11 of *Algorithmic Game Theory***.  A finite two-person
zero-sum game, given by a payoff matrix `A` (the amount the column player
pays the row player), has optimal mixed strategies: mixed strategies `p` for
the row player and `q` for the column player forming a saddle point — `p`
maximizes the expected payment against `q`, and `q` minimizes it against
`p` — and the pair `(p, q)` is a mixed Nash equilibrium of the two-player
game in which the row player's payoff is `A x y` and the column player's is
`-A x y`.  Consequently the game has a value; the book obtains the pair as
the optimal solutions of a dual pair of linear programs.

The strategy sets are `Fin (m + 1)` and `Fin (n + 1)` so that both players
have at least one strategy; over an empty strategy set `stdSimplex` is empty
and no saddle point exists. -/
theorem zero_sum_minimax {m n : ℕ} (A : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) :
    ∃ p ∈ stdSimplex ℝ (Fin (m + 1)), ∃ q ∈ stdSimplex ℝ (Fin (n + 1)),
      (∀ p' ∈ stdSimplex ℝ (Fin (m + 1)),
        p' ⬝ᵥ A.mulVec q ≤ p ⬝ᵥ A.mulVec q) ∧
      (∀ q' ∈ stdSimplex ℝ (Fin (n + 1)),
        p ⬝ᵥ A.mulVec q ≤ p ⬝ᵥ A.mulVec q') ∧
      IsMixedNash (zeroSumPayoff A) (matrixGameProfile p q) := by
  sorry

end AGT
