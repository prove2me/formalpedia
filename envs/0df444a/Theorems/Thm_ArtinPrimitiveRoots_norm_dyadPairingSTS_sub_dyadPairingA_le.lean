-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_norm_dyadPairingSTS_sub_dyadPairingA_le
-- name    : ArtinPrimitiveRoots.norm_dyadPairingSTS_sub_dyadPairingA_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T00:25:09.582996+00:00
-- url     : https://prove2.me/theorems/a7709985-b4d6-4b73-8e4d-22936d990a28
-- title:
--   [21] (4.56)–(4.57) — removing the goodness projections changes the pairing ⟨f, STSf⟩ at dyad 2^k by at most c·2^kYH_mH_n·L^{−A}
-- statement:
--   Fix $\delta > 0$, $C$, $c_1$, $c_2$. For every $A_0 > 0$, $K \ge 1$, band exponents $0.1 < a_1 < \dots < a_K < 0.2$ and $A > 0$ there are $c$ and $x_0$ such that the following holds for $x \ge x_0$, $H_m, H_n \ge x^\delta$ with $c_1x \le H_mH_n \le c_2x$, and every $Y \ge 1$ and $k$. Take $\alpha$ supported on $W$-rough integers of an interval inside $[H_m, 2H_m]$, $\beta$ supported on $W$-rough integers of $[H_n, 2H_n]$, and both bounded by $(\log x)^C$. Then
--
--   $$\|\texttt{dyadPairingSTS} - \texttt{dyadPairingA}\| \le c\,2^kYH_mH_n(\log x)^{-A}.$$
--
--   These are the pairings $\langle f, STSf\rangle_\sigma$ and $\langle f, Af\rangle_\sigma$, with $A = GSTSG$, at the pad dyad $2^k$ (bundle `Def_ArtinMinorOperator`).
--
--   Source: [21] = OpenAI, *The Poisson–Dirichlet law for prime predecessors* (2026), pp. 31–32, (4.56)–(4.57).
-- source:
--   OpenAI, The Poisson-Dirichlet law for prime predecessors, OpenAI Math Release preprint, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/paper.pdf (Apache-2.0), p. 31–32, (4.56)–(4.57)

import Mathlib
import Definitions.Def_ArtinSieve
import Definitions.Def_ArtinMinorOperator

namespace ArtinPrimitiveRoots

open Real

theorem norm_dyadPairingSTS_sub_dyadPairingA_le (δ C c₁ c₂ : ℝ) (hδ : 0 < δ) :
    ∀ A₀ : ℝ, 0 < A₀ → ∀ K : ℕ, 1 ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∀ A : ℝ, 0 < A →
      ∃ c x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
        c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x →
        ∀ α β : ℕ → ℂ,
          (∃ J : Set ℝ, J.OrdConnected ∧ J ⊆ Set.Icc Hm (2 * Hm) ∧
            ∀ m, α m ≠ 0 → (m : ℝ) ∈ J ∧ IsRough (sieveLevel x) m) →
          (∀ n, β n ≠ 0 → Hn ≤ n ∧ (n : ℝ) ≤ 2 * Hn ∧ IsRough (sieveLevel x) n) →
          (∀ m, ‖α m‖ ≤ log x ^ C) → (∀ n, ‖β n‖ ≤ log x ^ C) →
          ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
            ‖dyadPairingSTS x a A₀ Y Hm Hn α β k - dyadPairingA x a A₀ Y Hm Hn α β k‖ ≤
              c * (2 ^ k * Y * Hm * Hn * log x ^ (-A)) := by
  sorry

end ArtinPrimitiveRoots
