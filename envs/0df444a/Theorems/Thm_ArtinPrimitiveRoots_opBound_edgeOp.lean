-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_opBound_edgeOp
-- name    : ArtinPrimitiveRoots.opBound_edgeOp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T00:24:13.1004+00:00
-- url     : https://prove2.me/theorems/57d90f8e-cc0e-4c87-8f0f-b87ed19efcf5
-- title:
--   [21] (4.23)–(4.42) — for every G one can choose A₀, then K₀, so that every edge E_j has norm at most L^{−G} on the memory space
-- statement:
--   Fix $\delta$, $c_1$, $c_2$. For every $G > 0$ there are $A_0 > 0$ and $K_0$ such that for every $K \ge \max(1, K_0)$ and all band exponents $0.1 < a_1 < \dots < a_K < 0.2$ there is $x_0$ with the following property. Take $x \ge x_0$, $H_m, H_n \ge x^\delta$ with $c_1x \le H_mH_n \le c_2x$, $Y \ge 1$, a dyad $k$, $P = $ `dyadParams x a A₀ Y Hm Hn k`, a root $\omega$ of the box and $j < N$. Then the edge `edgeOp ω j` has operator norm at most $(\log x)^{-G}$ on $\ell^2$ of the states with weight `stWeight` (`OpBound`, bundle `Def_ArtinMemoryModel`).
--
--   Source: [21] = OpenAI, *The Poisson–Dirichlet law for prime predecessors* (2026), pp. 24–29, (4.23)–(4.42).
-- source:
--   OpenAI, The Poisson-Dirichlet law for prime predecessors, OpenAI Math Release preprint, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/paper.pdf (Apache-2.0), p. 24–29, (4.23)–(4.42)

import Mathlib
import Definitions.Def_ArtinMemoryModel

namespace ArtinPrimitiveRoots

open Real

theorem opBound_edgeOp (δ c₁ c₂ : ℝ) :
    ∀ G : ℝ, 0 < G → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ, ∀ K : ℕ, 1 ≤ K → K₀ ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
        c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x → ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
          let P := dyadParams x a A₀ Y Hm Hn k
          ∀ ω, P.RootIn ω → ∀ j < P.N, P.OpBound (P.edgeOp ω j) (log x ^ (-G)) := by
  sorry

end ArtinPrimitiveRoots
