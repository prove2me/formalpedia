-- Prove2me | Theorems.Thm_ARTreeCover_Supplement_theorem_41
-- name    : ARTreeCover.Supplement.theorem_41
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:13:59.278438+00:00
-- url     : https://prove2.me/theorems/c0bfc78f-3b26-4b76-83fe-15dfdb9fc3d5
-- title:
--   Theorem 41 — connected $K_r$-minor-free graphs have almost-Ramsey embeddings into $\ell_q^{O(\log n)}$: three trade-offs
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Let $G$ be a connected $n$-vertex weighted $K_r$-minor-free graph, $k>0$ an integer, $\Delta>0$, $q\in[1,\infty]$ and $L(n)=\max(1,\log_2n)$. For each pair $(\alpha,s)$ below there are $D\le C\,L(n)$ and an almost-Ramsey embedding $f:V\to\ell_q^D$ for scale $\Delta$ satisfying at least $n/s$ vertices with distortion $\alpha$:
--
--   1. $\alpha=C$ and $s=C\,r^4$;
--   2. $\alpha=Ck$ and $s=C\,r^{1/k}L(n)$;
--   3. $\alpha=Cr$ and $s=C\,r^2$.
--
--   Differences from the source:
--   - encoding: O(·) and Ω(·) → one absolute constant C > 0 chosen before every other quantifier; O(x) is C·x and Ω(x) is x/C; reason: the standard reading of asymptotic bounds with absolute constants; one constant for several O(·) is the same as several, since a larger C weakens every bound
--   - reading: log n inside the bound → L(n) = max(1, log₂ n); reason: equal to log₂ n for n ≥ 2; at n = 1 the printed log n is 0, which would make the bound 0 (or divide by 0) on a one-vertex graph
--   - encoding: ℓ_q^{O(log n)}, 1 ≤ q ≤ ∞ → PiLp q (Fin D → ℝ) with D ≤ C·L(n), q : ℝ≥0∞ with 1 ≤ q; reason: the same spaces; q = ∞ is the sup norm, and the dimension bound is uniform in q
--   - encoding: "for every real parameter ϵ > 0" (resp. 0 < ϵ ≤ 1) in the hypotheses → no ϵ binder; reason: ϵ does not occur in the conclusion, so the statement for every such ϵ is equivalent to the statement without it
-- source:
--   Elkin, Shabat, Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings, STOC 2027 submission (manuscript sha256 8ce8e6be…), Theorem 41, pp.50–51 (PDF pp.53–54)

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_ARTreeCover_logL
import Definitions.Def_ARTreeCover_Supplement_KrMinorFree
import Definitions.Def_ARTreeCover_Supplement_IsAlmostRamseyEmbedding

open scoped ENNReal

namespace ARTreeCover.Supplement

open ARTreeCover

/-- **Theorem 41**, pp.50–51 (PDF pp.53–54). Elkin, Shabat, *Near-Optimal Almost-Ramsey Spanning Tree Covers, via Layered Clusterings*,
STOC 2027 submission (manuscript sha256 8ce8e6be…).

"Let G be a connected n-vertex Kr-minor-free graph, let k > 0 be an integer, and let 0 < ϵ ≤ 1,
∆ > 0, and 1 ≤ q ≤ ∞ be real parameters. Then, G admits an almost-Ramsey embedding
f : V → ℓ_q^{O(log n)} for scale ∆, that satisfies n/s vertices with stretch α, for every choice of
the following pairs of values for α and s.
1. α = O(1) and s = O(r⁴),
2. α = O(k) and s = O(r^{1/k} log n),
3. α = O(r) and s = O(r²)."

**Formalization Note.**
1. One absolute `C > 0`, chosen before every other parameter, serves every O(·), including the
   stretches. `L(n) = max(1, log₂ n)`. "Stretch" is the distortion of Definition 23.
2. `ℓ_q^{O(log n)}` is `PiLp q (fun _ : Fin D => ℝ)` with `D ≤ C · L(n)`, for every
   `q ∈ [1, ∞]` (`q : ℝ≥0∞` with `Fact (1 ≤ q)`, `q = ∞` the sup norm); the dimension bound is part of
   the conclusion and uniform in `q`.
3. The printed `0 < ϵ ≤ 1` does not occur in the conclusion; the binder is dropped (equivalent). -/
theorem theorem_41 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (V : Type) [Fintype V] (G : WGraph V) (r k : ℕ) (Δ : ℝ),
        0 < k → 0 < Δ → G.graph.Connected → KrMinorFree r G →
        (∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], ∃ D : ℕ, (D : ℝ) ≤ C * logL (Fintype.card V) ∧
            ∃ f : V → PiLp q (fun _ : Fin D => ℝ), IsAlmostRamseyEmbedding G f Δ ((Fintype.card V : ℝ) / (C * (r : ℝ) ^ 4)) (C)) ∧
        (∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], ∃ D : ℕ, (D : ℝ) ≤ C * logL (Fintype.card V) ∧
            ∃ f : V → PiLp q (fun _ : Fin D => ℝ), IsAlmostRamseyEmbedding G f Δ ((Fintype.card V : ℝ) / (C * (r : ℝ) ^ ((1 : ℝ) / k) * logL (Fintype.card V))) (C * k)) ∧
        (∀ (q : ℝ≥0∞) [Fact (1 ≤ q)], ∃ D : ℕ, (D : ℝ) ≤ C * logL (Fintype.card V) ∧
            ∃ f : V → PiLp q (fun _ : Fin D => ℝ), IsAlmostRamseyEmbedding G f Δ ((Fintype.card V : ℝ) / (C * (r : ℝ) ^ 2)) (C * r)) := by sorry

end ARTreeCover.Supplement
