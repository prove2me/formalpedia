-- Prove2me | Theorems.Thm_AGT_deterministic_regret_lower
-- name    : AGT.deterministic_regret_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-12T03:32:21.131214+00:00
-- url     : https://prove2.me/theorems/d532a552-82aa-483f-a9ac-235361a24f18
-- title:
--   Deterministic algorithms have linear regret
-- statement:
--   Deterministic algorithms cannot avoid linear regret (Theorem 4.3 of *Algorithmic Game Theory*). For every deterministic online algorithm $D$ on $N = n+1$ actions there is a single $\{0,1\}$-valued loss sequence $\ell$ such that, at every horizon $T$ simultaneously,
--
--   1. $D$'s cumulative loss is exactly $T$ — the adversary charges loss $1$ to precisely the action $D$ is about to select and $0$ to all others;
--   2. some action $k$ (depending on the horizon) has cumulative loss at most $\lfloor T/N\rfloor$ — by pigeonhole, some action is selected at most $\lfloor T/N\rfloor$ times, and only selected actions are ever charged.
--
--   Hence randomization is necessary for sublinear regret, which is why the chapter's algorithms play distributions.
--
--   *A note on the rendering.* The book prints $L^T_{\min} = \lfloor T/N\rfloor$; its proof establishes $\le$, which is the direction the lower bound needs, so the formal statement asserts the inequality. The single sequence works for all horizons at once because the adversary's construction never consults $T$. The bound uses natural-number floor division, exactly as printed.
-- source:
--   N. Nisan, T. Roughgarden, E. Tardos, V. V. Vazirani (eds.), Algorithmic Game Theory, Cambridge University Press 2007, https://doi.org/10.1017/CBO9780511800481, Section 4.3.1, Theorem 4.3, pp. 83-84

import Definitions.Def_agt_regret

namespace AGT

/-- **Theorem 4.3 of *Algorithmic Game Theory***: deterministic algorithms
cannot have sublinear external regret.  For every deterministic online
algorithm `D` on `n + 1` actions there is a `{0,1}`-valued loss sequence on
which `D` suffers loss `T` at every horizon `T` while some single action
suffers loss at most `⌊T/(n+1)⌋`.

The adversary simply charges loss `1` to the action `D` is about to play and
`0` to all others; the conclusion `≤ ⌊T/(n+1)⌋` is what that construction
yields (the book prints `=`, but its proof establishes the inequality, which
is the usable direction). -/
theorem deterministic_regret_lower {n : ℕ}
    (D : List (Fin (n + 1) → ℝ) → Fin (n + 1)) :
    ∃ ℓ : ℕ → Fin (n + 1) → ℝ,
      (∀ t i, ℓ t i = 0 ∨ ℓ t i = 1) ∧
      (∀ T : ℕ, ∑ t ∈ Finset.range T, ℓ t (detPlay D ℓ t) = T) ∧
      (∀ T : ℕ, ∃ k : Fin (n + 1), actionLoss ℓ k T ≤ ((T / (n + 1) : ℕ) : ℝ)) := by
  sorry

end AGT
