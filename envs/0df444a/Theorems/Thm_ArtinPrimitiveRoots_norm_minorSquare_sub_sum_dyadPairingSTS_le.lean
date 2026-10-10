-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_norm_minorSquare_sub_sum_dyadPairingSTS_le
-- name    : ArtinPrimitiveRoots.norm_minorSquare_sub_sum_dyadPairingSTS_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T00:22:54.048714+00:00
-- url     : https://prove2.me/theorems/b7adef84-0d42-4d32-8856-7ed176bcda62
-- title:
--   [21] (4.58)–(4.63) — Q_Y^min equals Σ_{k ≤ ⌊L⌋} 2^{−k}⟨f, STSf⟩ at dyad 2^k, up to c·H_mH_nY·L^{−A}
-- statement:
--   Fix $\delta$, $C$, $c_1 > 0$ and $c_2$. For every $A_0 > 0$, $K \ge 1$, band exponents $0.1 < a_1 < \dots < a_K < 0.2$ and $A > 0$ there are $c$ and $x_0$ such that the following holds for $x \ge x_0$, $H_m, H_n \ge x^\delta$ with $c_1x \le H_mH_n \le c_2x$, and every $Y \ge 1$. The coefficients are as in Lemma 10.2: $\alpha$ supported on $W$-rough integers of an interval inside $[H_m, 2H_m]$, $\beta$ on $W$-rough integers of $[H_n, 2H_n]$, both bounded by $(\log x)^C$. Then
--
--   $$\Bigl\|Q_Y^{\min} - \sum_{k=0}^{\lfloor \log x\rfloor} 2^{-k}\,\texttt{dyadPairingSTS}_k\Bigr\| \le c\,H_mH_nY(\log x)^{-A},$$
--
--   where $Q_Y^{\min}$ is `minorSquare` (bundle `Def_ArtinMinorSquare`) and $\texttt{dyadPairingSTS}_k$ is the pairing $\langle f, STSf\rangle_\sigma$ at the pad dyad $2^k$ (bundle `Def_ArtinMinorOperator`).
--
--   Source: [21] = OpenAI, *The Poisson–Dirichlet law for prime predecessors* (2026), pp. 32–33, (4.58)–(4.63).
-- source:
--   OpenAI, The Poisson-Dirichlet law for prime predecessors, OpenAI Math Release preprint, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/paper.pdf (Apache-2.0), p. 32–33, (4.58)–(4.63)

import Mathlib
import Definitions.Def_ArtinSieve
import Definitions.Def_ArtinMinorSquare
import Definitions.Def_ArtinMinorOperator

namespace ArtinPrimitiveRoots

open Real Finset

theorem norm_minorSquare_sub_sum_dyadPairingSTS_le (δ C c₁ c₂ : ℝ) (hc₁ : 0 < c₁) :
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
          ∀ Y : ℝ, 1 ≤ Y →
            ‖minorSquare x a A₀ Y Hm Hn α β - ∑ k ∈ range (⌊log x⌋₊ + 1),
                ((2 : ℂ) ^ k)⁻¹ * dyadPairingSTS x a A₀ Y Hm Hn α β k‖ ≤
              c * (Hm * Hn * Y * log x ^ (-A)) := by
  sorry

end ArtinPrimitiveRoots
