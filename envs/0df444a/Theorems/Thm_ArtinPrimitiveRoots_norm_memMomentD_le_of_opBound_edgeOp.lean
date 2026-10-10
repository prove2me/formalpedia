-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_norm_memMomentD_le_of_opBound_edgeOp
-- name    : ArtinPrimitiveRoots.norm_memMomentD_le_of_opBound_edgeOp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T00:22:44.15704+00:00
-- url     : https://prove2.me/theorems/acbd61d6-db02-40a9-b7ae-21fa504e72a2
-- title:
--   [21] (4.43)–(4.55) — if every edge has norm at most L^{−G}, the memory moment with global birth distinctness is at most L^{−(G−1)N}
-- statement:
--   Fix $\delta$, $c_1$, $c_2$. Take $G > 0$, $A_0 > 0$, $K \ge 1$ and band exponents $0.1 < a_1 < \dots < a_K < 0.2$. Suppose that for all large $x$ every edge has norm at most $(\log x)^{-G}$, as in `opBound_edgeOp`. Then there is $x_0$ such that for $x \ge x_0$, $H_m, H_n \ge x^\delta$ with $c_1x \le H_mH_n \le c_2x$, $Y \ge 1$, every dyad $k$ and every root $\omega$ of the box,
--
--   $$\|\texttt{memMomentD}(\omega)\| \le (\log x)^{-(G-1)N}$$
--
--   for $P = $ `dyadParams x a A₀ Y Hm Hn k`.
--
--   No hypothesis on the ghosts is needed: their norms are bounded inside the proof.
--
--   Source: [21] = OpenAI, *The Poisson–Dirichlet law for prime predecessors* (2026), pp. 29–31, (4.43)–(4.55).
-- source:
--   OpenAI, The Poisson-Dirichlet law for prime predecessors, OpenAI Math Release preprint, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/paper.pdf (Apache-2.0), p. 29–31, (4.43)–(4.55)

import Mathlib
import Definitions.Def_ArtinMemoryModel

namespace ArtinPrimitiveRoots

open Real

theorem norm_memMomentD_le_of_opBound_edgeOp (δ c₁ c₂ : ℝ) :
    ∀ G : ℝ, 0 < G → ∀ A₀ : ℝ, 0 < A₀ → ∀ K : ℕ, 1 ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      (∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
        c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x → ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
          let P := dyadParams x a A₀ Y Hm Hn k
          ∀ ω, P.RootIn ω → ∀ j < P.N, P.OpBound (P.edgeOp ω j) (log x ^ (-G))) →
      ∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
        c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x → ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
          let P := dyadParams x a A₀ Y Hm Hn k
          ∀ ω, P.RootIn ω → ‖P.memMomentD ω‖ ≤ log x ^ (-((G - 1) * P.N)) := by
  sorry

end ArtinPrimitiveRoots
