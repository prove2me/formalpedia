-- Prove2me | Theorems.Thm_ARTreeCover_theorem_17
-- name    : ARTreeCover.theorem_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:53:29.061981+00:00
-- url     : https://prove2.me/theorems/e79e8d0b-2553-4856-8cb5-3c9681106802
-- title:
--   Theorem 17: $(O(kN^{1/k}),k-1)$-network decompositions
-- statement:
--   There is an absolute constant $C>0$ such that for every $N$-vertex unweighted graph $L$ and every integer $k\ge 1$ there is $Z\le C\,k\,N^{1/k}$ and a strong $(Z,k-1)$-network decomposition of $L$.
--
--   This is the theorem of Linial and Saks with $p=N^{-1/k}$; Appendix B of the paper gives a proof with $Z=\lceil 4kN^{1/k}\rceil$. It is the combinatorial input of the layered neighborhood covers of Theorem 11, Item 1.
--
--   Differences from the source:
--   - encoding: O(·) in the size bound → one absolute constant C > 0 chosen before every other quantifier; reason: the paper's constants are absolute (⌈3 ln n/p⌉, ⌈4kn^{1/k}⌉ layers, O(ϵ⁻¹log(n/ϵ)) scales); this is the standard reading
--   - reading: a parameter k ≥ 1 → a natural number k ≥ 1; reason: Appendix B picks r ∈ {0, 1, …, k − 1}, and the radius k − 1 and the source (Linial–Saks with p = N^{−1/k}) concern integer k
--   - encoding: a coloring f : V → {1, …, Z} whose monochromatic components have strong radius at most Γ (Definition 13) → f : V → Fin Z, and for every vertex x of color c some vertex z of color c with hop distance (`SimpleGraph.edist` in L[f⁻¹(c)]) at most Γ to every vertex of x's component; reason: Fin Z is {1, …, Z} shifted by one; such a z lies in the component, so it is a center in L[f⁻¹(c)]
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Theorem 17, p.25 (PDF p.28); proof in Appendix B, pp.XIV–XVI (PDF pp.73–75)

import Mathlib
import Definitions.Def_ARTreeCover_IsNetworkDecomp

namespace ARTreeCover

/-- **Theorem 17**, p.25 (PDF p.28); proof in Appendix B, pp.XIV–XVI (PDF pp.73–75). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"Theorem 17 (Theorem 2.1 in [52], for p = N^{−1/k}). Any N-vertex unweighted graph admits a
(O(kN^{1/k}), k − 1)-network decomposition, for any choice of a parameter k ≥ 1."

**Formalization Note.** The graph is a `SimpleGraph` on a finite type with `N = Fintype.card V`
vertices. `k` is a natural number (Appendix B picks `r ∈ {0, 1, …, k − 1}`), so `k − 1` is the
natural-number difference, exact for `k ≥ 1`. `O(kN^{1/k})` is `C · k · N^{1/k}` with one absolute
`C > 0` chosen before the graph and `k`. The radius is in hops inside each monochromatic
component (`IsNetworkDecomp`). -/
theorem theorem_17 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] (L : SimpleGraph V) (k : ℕ), 1 ≤ k →
        ∃ Z : ℕ, (Z : ℝ) ≤ C * k * (Fintype.card V : ℝ) ^ ((1 : ℝ) / k) ∧
          ∃ f : V → Fin Z, IsNetworkDecomp L Z (k - 1) f := by sorry

end ARTreeCover
