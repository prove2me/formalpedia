-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_re_dyadMoment_le
-- name    : ArtinPrimitiveRoots.re_dyadMoment_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T00:22:10.917185+00:00
-- url     : https://prove2.me/theorems/04ec0413-1555-4590-85db-475fdfe7b547
-- title:
--   [21] (4.1), Proposition 4.1 — for every E₀ one can choose A₀, then K₀, so that the dyadic moment of (AA*)^R is at most U·V·L^{−2R·E₀}
-- statement:
--   Fix $\delta > 0$, $c_1$, $c_2$. For every $E_0 > 0$ there are $A_0 > 0$ and $K_0$ such that for every $K \ge \max(1, K_0)$ and all band exponents $0.1 < a_1 < \dots < a_K < 0.2$ there is $x_0$ with the following property. For $x \ge x_0$, $H_m, H_n \ge x^\delta$ with $c_1x \le H_mH_n \le c_2x$, every $Y \ge 1$ and every $k$, the real part of `dyadMoment x a A₀ Y Hm Hn k` is at most $2^kYH_mH_n(\log x)^{-2RE_0}$, with $R = $ `momentPower x`.
--
--   `dyadMoment` is the moment $\sum_P \langle u_P, (AA^*)^R u_P\rangle_\sigma$ of the operator $A = GSTSG$ at the pad dyad $d_0 = 2^k$, with $U = 2^kYH_m$ and $V = H_n$ (bundle `Def_ArtinMinorOperator`).
--
--   Source: [21] = OpenAI, *The Poisson–Dirichlet law for prime predecessors* (2026), p. 19, Proposition 4.1, (4.1).
-- source:
--   OpenAI, The Poisson-Dirichlet law for prime predecessors, OpenAI Math Release preprint, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/paper.pdf (Apache-2.0), p. 19, Proposition 4.1, (4.1)

import Mathlib
import Definitions.Def_ArtinMinorOperator

namespace ArtinPrimitiveRoots

open Real

theorem re_dyadMoment_le (δ c₁ c₂ : ℝ) (hδ : 0 < δ) :
    ∀ E₀ : ℝ, 0 < E₀ → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
        c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x → ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
          (dyadMoment x a A₀ Y Hm Hn k).re ≤
            2 ^ k * Y * Hm * Hn * log x ^ (-(E₀ * (2 * momentPower x))) := by
  sorry

end ArtinPrimitiveRoots
