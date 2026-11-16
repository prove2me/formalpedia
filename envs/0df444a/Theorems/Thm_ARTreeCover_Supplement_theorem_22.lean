-- Prove2me | Theorems.Thm_ARTreeCover_Supplement_theorem_22
-- name    : ARTreeCover.Supplement.theorem_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:07:59.95453+00:00
-- url     : https://prove2.me/theorems/b6037894-bd59-4759-856e-f2e6ffb44c9a
-- title:
--   Theorem 22 — $K_r$-minor-free graphs have almost-Ramsey tree and HST covers: four stretch/size trade-offs
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $G$ be an $n$-vertex weighted $K_r$-minor-free graph, $k>0$ an integer, $0<\epsilon\le1$ and $L(n)=\max(1,\log_2n)$. For each of the following pairs $(\alpha,M)$, $G$ admits a (not necessarily spanning) almost-Ramsey tree cover and an almost-Ramsey HST cover, both with stretch $\alpha$ and size at most $M$:
--
--   1. $\alpha=8+\epsilon$ and $M=(C/\epsilon)^{r+1}L(n)$;
--   2. $\alpha=16+\epsilon$ and $M=C\,r^4L(n)/\epsilon^3$;
--   3. $\alpha=Ck$ and $M=C\,r^{1/k}L(n)^2$;
--   4. $\alpha=Cr$ and $M=C\,r^2L(n)$.
--
--   The trees need not be subgraphs of $G$, and $G$ need not be connected.
--
--   Differences from the source:
--   - encoding: O(·) and Ω(·) → one absolute constant C > 0 chosen before every other quantifier; O(x) is C·x and Ω(x) is x/C; reason: the standard reading of asymptotic bounds with absolute constants; one constant for several O(·) is the same as several, since a larger C weakens every bound
--   - encoding: O(1/ϵ)^{r+1} → (C/ϵ)^{r+1}; reason: the constant sits inside the power as printed
--   - reading: log n inside the bound → L(n) = max(1, log₂ n); reason: equal to log₂ n for n ≥ 2; at n = 1 the printed log n is 0, which would make the bound 0 (or divide by 0) on a one-vertex graph
--   - encoding: a (not necessarily spanning) tree T = (V, E′) → a published WForest (weights in (0, ∞]) whose graph is preconnected; reason: on the nonempty vertex set of a connected graph this is a tree on V; edges outside G with any positive weight are allowed (footnote 13, p.28)
--   - encoding: almost-Ramsey forest/HST cover with stretch α → the cover predicate, the stretch predicate and the almost-Ramsey predicate with the same α; reason: almost-Ramsey with stretch α implies stretch α (take ∆ = d_G(u, v)); the published theorem_19 uses the same encoding
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Theorem 22, pp.35–36 (PDF pp.38–39)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_logL
import Definitions.Def_ARTreeCover_WForest
import Definitions.Def_ARTreeCover_HST
import Definitions.Def_ARTreeCover_IsForestCover
import Definitions.Def_ARTreeCover_IsHSTCover
import Definitions.Def_ARTreeCover_Supplement_KrMinorFree

open scoped ENNReal

namespace ARTreeCover.Supplement

open ARTreeCover

/-- **Theorem 22**, pp.35–36 (PDF pp.38–39). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"Let G be an n-vertex Kr-minor-free graph, let k > 0 be an integer, and let 0 < ϵ ≤ 1 be a real
parameter. The graph G admits a (not necessarily spanning) almost-Ramsey tree cover T and an
almost-Ramsey HST cover H, both with stretch α and size M, for every choice of the following pairs
of values for α and M.
1. (Item (3) in Theorem 11) α = 8 + ϵ and M = O(1/ϵ)^{r+1} · log n,
2. (Item (4) in Theorem 11) α = 16 + ϵ and M = O(r⁴ · log n / ϵ³),
3. (Theorem 14) α = O(k) and M = O(r^{1/k} log² n),
4. (Item (2) in Theorem 11) α = O(r) and M = O(r² log n)."

**Formalization Note.**
1. One absolute `C > 0`, chosen before every other parameter, serves every O(·), including the
   stretches `O(k)`, `O(r)`. `O(1/ϵ)^{r+1}` is `(C/ϵ)^{r+1}`, the constant inside the power as
   printed. `L(n) = max(1, log₂ n)`.
2. A tree is a published `WForest` whose graph is preconnected (edges may be non-edges of `G`,
   weights in `(0, ∞]`); `G` need not be connected. Each item is a separate pair of covers.
3. Almost-Ramsey covers are also stated with stretch, which almost-Ramsey implies. -/
theorem theorem_22 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] (G : WGraph V) (r k : ℕ) (ε : ℝ),
        0 < k → 0 < ε → ε ≤ 1 → KrMinorFree r G →
        ((∃ m : ℕ, (m : ℝ) ≤ (C / ε) ^ (r + 1) * logL (Fintype.card V) ∧ ∃ T : Fin m → WForest V,
            (∀ i, (T i).graph.Preconnected) ∧
            IsForestCover G T ∧
            ForestStretchLE G T (8 + ε) ∧
            ForestAlmostRamsey G T (8 + ε)) ∧
          (∃ m : ℕ, (m : ℝ) ≤ (C / ε) ^ (r + 1) * logL (Fintype.card V) ∧ ∃ H : Fin m → HST V,
            IsHSTCover G H ∧
            HSTStretchLE G H (8 + ε) ∧
            HSTAlmostRamsey G H (8 + ε))) ∧
        ((∃ m : ℕ, (m : ℝ) ≤ C * (r : ℝ) ^ 4 * logL (Fintype.card V) / ε ^ 3 ∧ ∃ T : Fin m → WForest V,
            (∀ i, (T i).graph.Preconnected) ∧
            IsForestCover G T ∧
            ForestStretchLE G T (16 + ε) ∧
            ForestAlmostRamsey G T (16 + ε)) ∧
          (∃ m : ℕ, (m : ℝ) ≤ C * (r : ℝ) ^ 4 * logL (Fintype.card V) / ε ^ 3 ∧ ∃ H : Fin m → HST V,
            IsHSTCover G H ∧
            HSTStretchLE G H (16 + ε) ∧
            HSTAlmostRamsey G H (16 + ε))) ∧
        ((∃ m : ℕ, (m : ℝ) ≤ C * (r : ℝ) ^ ((1 : ℝ) / k) * logL (Fintype.card V) ^ 2 ∧ ∃ T : Fin m → WForest V,
            (∀ i, (T i).graph.Preconnected) ∧
            IsForestCover G T ∧
            ForestStretchLE G T (C * k) ∧
            ForestAlmostRamsey G T (C * k)) ∧
          (∃ m : ℕ, (m : ℝ) ≤ C * (r : ℝ) ^ ((1 : ℝ) / k) * logL (Fintype.card V) ^ 2 ∧ ∃ H : Fin m → HST V,
            IsHSTCover G H ∧
            HSTStretchLE G H (C * k) ∧
            HSTAlmostRamsey G H (C * k))) ∧
        ((∃ m : ℕ, (m : ℝ) ≤ C * (r : ℝ) ^ 2 * logL (Fintype.card V) ∧ ∃ T : Fin m → WForest V,
            (∀ i, (T i).graph.Preconnected) ∧
            IsForestCover G T ∧
            ForestStretchLE G T (C * r) ∧
            ForestAlmostRamsey G T (C * r)) ∧
          (∃ m : ℕ, (m : ℝ) ≤ C * (r : ℝ) ^ 2 * logL (Fintype.card V) ∧ ∃ H : Fin m → HST V,
            IsHSTCover G H ∧
            HSTStretchLE G H (C * r) ∧
            HSTAlmostRamsey G H (C * r))) := by sorry

end ARTreeCover.Supplement
