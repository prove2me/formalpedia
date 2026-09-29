-- Prove2me | Theorems.Thm_AGT_constant_sum_external_regret
-- name    : AGT.constant_sum_external_regret
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-12T03:32:50.416901+00:00
-- url     : https://prove2.me/theorems/bab69340-ea5b-4524-bdf2-8c1f37404f94
-- title:
--   No-regret play attains the value of a constant-sum game
-- statement:
--   A player who follows a no-external-regret procedure in a constant-sum game loses, on average, at most the value of the game plus a vanishing overhead (Theorem 4.9 of *Algorithmic Game Theory*). Player $i$'s losses are given by a matrix $S$ ($S_{ky}$ is $i$'s loss playing $k$ against the opponent's $y$), and $v$ is a **security level** for player $i$: some mixed strategy $p$ satisfies $\sum_k p_k S_{ky} \le v$ against every opponent action $y$ — for the game value $v_i$ of a constant-sum game this is exactly what the minimax theorem (Theorem 1.11, Mission I of this series) provides. The opponent plays arbitrary mixed actions $q^t$, so the loss vector the online procedure faces at time $t$ is $\ell^t = S q^t$. If the procedure's external regret on that sequence at horizon $T$ is at most $R$, then its cumulative loss is at most $vT + R$ — an average of $v + R/T$ per round.
--
--   *A note on the rendering.* Only player $i$'s loss matrix enters: the constant-sum structure of the book's setting is what makes the game have a value, and it enters the formal statement through the security-level hypothesis rather than through the opponent's payoffs, which the argument never touches. Nothing is assumed about the procedure beyond the regret bound itself — the played weights need not even be distributions — and $T = 0$ is allowed, where the regret hypothesis already forces $0 \le R$.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Section 4.4.2, Theorem 4.9, pp. 89-90

import Definitions.Def_agt_regret
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Matrix.Basic

namespace AGT

/-- **Theorem 4.9 of *Algorithmic Game Theory***: in a constant-sum game, a
player who plays with small external regret loses at most the value of the
game plus the regret overhead.

Player `i`'s losses are given by the matrix `S` (`S k y` is `i`'s loss when
playing `k` against the opponent's `y`), and `v` is a **security level** for
player `i`: some mixed strategy guarantees expected loss at most `v` against
every opponent action — for the game value `v_i` of a constant-sum game this
is exactly what the minimax theorem (Theorem 1.11 of this series) provides.
The opponent plays arbitrary mixed actions `q t`; the loss vector the
player's online procedure faces at time `t` is `ℓ t = S ·ᵥ q t`.  If the
procedure's external regret on that sequence at horizon `T` is at most `R`,
its cumulative loss is at most `v * T + R` — an average of `v + R/T`.

At `T = 0` the regret hypothesis forces `0 ≤ R` and the conclusion is
trivial, so no positivity of `T` is needed; the entries of `S` need not be
bounded, and nothing is assumed about the procedure beyond the regret
bound itself — the played weights need not even be distributions. -/
theorem constant_sum_external_regret {m n : ℕ}
    (S : Matrix (Fin (m + 1)) (Fin (n + 1)) ℝ) (v : ℝ)
    (hv : ∃ p ∈ stdSimplex ℝ (Fin (m + 1)),
      ∀ y : Fin (n + 1), ∑ k, p k * S k y ≤ v)
    (T : ℕ) (q : ℕ → Fin (n + 1) → ℝ) (hq : ∀ t, t < T → IsLottery (q t))
    (A : OnlineAlgorithm (m + 1)) (R : ℝ)
    (hreg : ∀ k, algLoss A (fun t => S.mulVec (q t)) T ≤
      actionLoss (fun t => S.mulVec (q t)) k T + R) :
    algLoss A (fun t => S.mulVec (q t)) T ≤ v * T + R := by
  sorry

end AGT
