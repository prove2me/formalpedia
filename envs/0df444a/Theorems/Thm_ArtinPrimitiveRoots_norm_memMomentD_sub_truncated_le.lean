-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_norm_memMomentD_sub_truncated_le
-- name    : ArtinPrimitiveRoots.norm_memMomentD_sub_truncated_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T00:23:49.709581+00:00
-- url     : https://prove2.me/theorems/a003eb2e-5096-4be6-b5fb-53bf6b611fe6
-- title:
--   [21] (4.16) — truncating the memory at ⌈L²⌉ changes the distinct memory moment by at most L^{−AN}
-- statement:
--   Fix $\delta$, $c_1$, $c_2$. For every $A > 0$, $A_0 > 0$, $K \ge 1$ and band exponents $0.1 < a_1 < \dots < a_K < 0.2$ there is $x_0$ with the following property. Take $x \ge x_0$, $H_m, H_n \ge x^\delta$ with $c_1x \le H_mH_n \le c_2x$, $Y \ge 1$, a dyad $k$, and $P = $ `dyadParams x a A₀ Y Hm Hn k`, whose memory bound is $\lceil(\log x)^2\rceil$. Then at every root $\omega$ of the box,
--
--   $$\bigl\|\texttt{memMomentD}_{B = \#\text{group primes}}(\omega) - \texttt{memMomentD}(\omega)\bigr\| \le (\log x)^{-AN}.$$
--
--   Source: [21] = OpenAI, *The Poisson–Dirichlet law for prime predecessors* (2026), p. 22, (4.16).
-- source:
--   OpenAI, The Poisson-Dirichlet law for prime predecessors, OpenAI Math Release preprint, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/paper.pdf (Apache-2.0), p. 22, (4.16)

import Mathlib
import Definitions.Def_ArtinMemoryModel

namespace ArtinPrimitiveRoots

open Real

theorem norm_memMomentD_sub_truncated_le (δ c₁ c₂ : ℝ) :
    ∀ A : ℝ, 0 < A → ∀ A₀ : ℝ, 0 < A₀ → ∀ K : ℕ, 1 ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
        c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x → ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
          let P := dyadParams x a A₀ Y Hm Hn k
          ∀ ω, P.RootIn ω →
            ‖(P.withB P.gPrimes.card).memMomentD ω - P.memMomentD ω‖ ≤ log x ^ (-(A * P.N)) := by
  sorry

end ArtinPrimitiveRoots
