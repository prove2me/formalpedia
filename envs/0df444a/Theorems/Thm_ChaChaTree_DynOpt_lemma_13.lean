-- Prove2me | Theorems.Thm_ChaChaTree_DynOpt_lemma_13
-- name    : ChaChaTree.DynOpt.lemma_13
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:22:39.722402+00:00
-- url     : https://prove2.me/theorems/268912bb-dbfa-4942-abf6-fe46b9e8f23b
-- title:
--   Lemma 13 — strictly independent families on the contracted and filtered instances lift to P with sizes adding
-- statement:
--   For a split of an instance $P$ with respect to $S = (S_1,\dots,S_k)$, let $\hat R$ be a strictly independent set of rectangles on $\hat P$ and $\check R_i$ a strictly independent set on $\check P_i$ for each $i \in [k]$. For $\hat r = \square_{\hat p, \hat q}$ on $\hat P$ let $s^{-1}(\hat r)$ be the unique rectangle $\square_{p,q}$ on $P$ with $s(p) = \hat p$, $s(q) = \hat q$. Then
--   $$R := \Big(\bigcup_{i\in[k]} \check R_i\Big) \cup s^{-1}(\hat R)$$
--   is a strictly independent set of rectangles on $P$, and $|R| = |\hat R| + \sum_{i\in[k]} |\check R_i|$.
--
--   Differences from the source:
--   - encoding: a partition S = (S_1, …, S_k) of [N] into disjoint contiguous intervals ordered from left to right → a segment map seg : ℕ → ℕ with IsSegmentation N k seg (monotone from [N] onto [k]; S_i = {x ∈ [N] | seg x = i}); reason: monotone and onto [k] is exactly a left-to-right partition into k nonempty contiguous intervals; same instances
--   - encoding: a rectangle □_{p,q} → the ordered pair (p, q) : Rect with IsRectOn P (p, q); reason: a rectangle is determined by its two defining points with p.y < q.y; same objects
--   - encoding: s⁻¹(R̂), the set of the unique preimages s⁻¹(r̂) of the rectangles r̂ ∈ R̂ → the set of pairs (p, q) ∈ P × P with (s(p), s(q)) ∈ R̂; reason: the same set: the uniqueness of the preimage is a property, and the cardinality claim is stated for this set
--   - encoding: the family {Ř_i}_{i∈[k]} → a function Rchk : ℕ → Finset Rect used on i ∈ [k]; reason: only the indices in [k] occur
-- source:
--   Čech, Haeupler, Roeyskoe, Rozhoň, Tarjan, Yingchareonthawornchai, Dynamic Optimality to within O(log log log n), STOC 2027 submission (manuscript, sha256 9316fbfd…7b9e), Lemma 13, p. 15 (PDF 16)

import Mathlib
import Definitions.Def_ChaChaTree_DynOpt_Instance
import Definitions.Def_ChaChaTree_DynOpt_Rectangles
import Definitions.Def_ChaChaTree_DynOpt_Split

set_option autoImplicit false

namespace ChaChaTree.DynOpt

/-- **Lemma 13** (p. 15). For a split of an instance `P` with respect to `S = (S₁, …, S_k)`, let
`R̂` be strictly independent on `P̂` and `Ř_i` strictly independent on `P̌_i` (`i ∈ [k]`). With
`s⁻¹(R̂)` the set of rectangles `□_{p,q}` on `P` with `□_{s(p),s(q)} ∈ R̂`, the set
`R := (⋃_{i∈[k]} Ř_i) ∪ s⁻¹(R̂)` is strictly independent on `P` and `|R| = |R̂| + Σ_{i∈[k]} |Ř_i|`. -/
theorem lemma_13 (N T : ℕ) (P : Finset (ℕ × ℕ)) (hP : IsInstance N T P) (k : ℕ) (seg : ℕ → ℕ)
    (hS : IsSegmentation N k seg) (Rhat : Finset Rect) (Rchk : ℕ → Finset Rect)
    (hRhat : IsStrictlyIndependent (contracted seg P) Rhat)
    (hRchk : ∀ i ∈ Finset.Icc 1 k, IsStrictlyIndependent (filtered seg P i) (Rchk i)) :
    IsStrictlyIndependent P ((Finset.Icc 1 k).biUnion Rchk ∪
        (P ×ˢ P).filter fun r => (segPoint seg r.1, segPoint seg r.2) ∈ Rhat) ∧
      ((Finset.Icc 1 k).biUnion Rchk ∪
          (P ×ˢ P).filter fun r => (segPoint seg r.1, segPoint seg r.2) ∈ Rhat).card =
        Rhat.card + ∑ i ∈ Finset.Icc 1 k, (Rchk i).card := by sorry

end ChaChaTree.DynOpt
