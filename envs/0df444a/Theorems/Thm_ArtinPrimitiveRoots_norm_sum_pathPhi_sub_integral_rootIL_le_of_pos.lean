-- Prove2me | Theorems.Thm_ArtinPrimitiveRoots_norm_sum_pathPhi_sub_integral_rootIL_le_of_pos
-- name    : ArtinPrimitiveRoots.norm_sum_pathPhi_sub_integral_rootIL_le_of_pos
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T00:29:40.737602+00:00
-- url     : https://prove2.me/theorems/ec964de2-66a9-4365-8486-a2171133bfbf
-- title:
--   [21] Lemma 3.4 — Σ over primitive roots of the path functional is (6/π²)UV ∫ of the independent-line moment over normalized roots, up to UV·L^{−AN}
-- statement:
--   Fix $\delta > 0$, $c_1$, $c_2$. For every $A > 0$, $A_0 > 0$, $K \ge 1$ and band exponents $0.1 < a_1 < \dots < a_K < 0.2$ there is $x_0$ with the following property. Take $x \ge x_0$, $H_m, H_n \ge x^\delta$ with $c_1x \le H_mH_n \le c_2x$, $Y \ge 1$ and a dyad $k$, and let $P$ be `dyadParams x a A₀ Y Hm Hn k`. Then
--
--   $$\Bigl\|\sum_{P_0 \in \mathrm{posBox}(U, V)}\mathrm{pathPhi}(\mathrm{rootOf}\,P_0, \mathrm{physDelta}\,P_0) - \frac{6}{\pi^2}UV\int_1^{16}\!\!\int_1^2\!\!\int_0^1\mathrm{rootIL}(Uu, Vv, r)\Bigr\| \le UV(\log x)^{-AN}.$$
--
--   Here $U, V, N$ are the fields of $P$ (bundle `Def_ArtinMemoryModel`). The hypothesis $\delta > 0$ makes the box side $U = 2^kYH_m \ge x^\delta$ a power of $x$, which the lattice count ([21] Lemma 3.3) needs; an earlier version of this statement omitted it.
--
--   Source: [21] = OpenAI, *The Poisson–Dirichlet law for prime predecessors* (2026), p. 17, Lemma 3.4.
-- source:
--   OpenAI, The Poisson-Dirichlet law for prime predecessors, OpenAI Math Release preprint, September 24, 2026, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/paper.pdf (Apache-2.0), p. 17, Lemma 3.4

import Mathlib
import Definitions.Def_ArtinMinorOperator
import Definitions.Def_ArtinMemoryModel

namespace ArtinPrimitiveRoots

open Real Finset

theorem norm_sum_pathPhi_sub_integral_rootIL_le_of_pos (δ c₁ c₂ : ℝ) (hδ : 0 < δ) :
    ∀ A : ℝ, 0 < A → ∀ A₀ : ℝ, 0 < A₀ → ∀ K : ℕ, 1 ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      ∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
        c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x → ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
          let P := dyadParams x a A₀ Y Hm Hn k
          ‖∑ P₀ ∈ posBox P.U P.V, P.pathPhi (rootOf P₀) (physDelta P₀) -
              ((6 / π ^ 2 * P.U * P.V : ℝ) : ℂ) *
                ∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1,
                  P.rootIL (P.U * u, P.V * v, r)‖ ≤
            P.U * P.V * log x ^ (-(A * P.N)) := by
  sorry

end ArtinPrimitiveRoots
