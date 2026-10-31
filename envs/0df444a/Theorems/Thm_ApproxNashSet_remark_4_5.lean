-- Prove2me | Theorems.Thm_ApproxNashSet_remark_4_5
-- name    : ApproxNashSet.remark_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:17:56.565545+00:00
-- url     : https://prove2.me/theorems/45616909-a3a1-4504-b500-eea108b274c2
-- title:
--   Remark 4.5 — if $\bar{\mathcal X}$ contains the generators of $\mathbb X$, every $x_{-i}$ lies in $\mathrm{conv}\{x^1_{-i},\dots,x^s_{-i}\}$
-- statement:
--   Let $\mathbb X=\operatorname{conv}V$ and let $G$ be a set of joint strategies with $V\subseteq G$ (for the step-1 point set $G=\bar{\mathcal X}$ this is the modification (12)). Then for every player $i$ and every $x\in\mathbb X$,
--   $$x_{-i}\in\operatorname{conv}\{z_{-i}:z\in G\}.$$
--
--   This is what lets the proof of Lemma 4.10 find, above the other players' strategies of any Pareto optimal point, a point of the inner approximation $P^{In}_i$.
--
--   Differences from the source:
--   - generalization: G = the finite set X̄ = {x¹, …, xˢ} produced by step 1, and the generators of X its vertices → any set G ⊇ V, and any generating set V with X = conv V; reason: the argument uses only V ⊆ G (from (12)) and X = conv V; the step-1 set is one such G
--   - generalization: N ≥ 2 players → any finite player type; reason: the statement concerns one player i and uses nothing about the others' number; N ≥ 2 is a special case
--   - encoding: objective space ℝ^{mᵢ} with ordering cone ℝ^{mᵢ}₊, strategy spaces Xᵢ = ℝ^{nᵢ}, players 1, …, N → Obj n i = (∏_{j≠i} ℝ^{nⱼ}) × (∏_{j≠i} ℝ^{nⱼ}) × ℝ with the componentwise order, Fin (n i) → ℝ, a finite type ι; reason: Lean convention; the same instances
-- source:
--   Feinstein–Hey–Rudloff, Approximating the set of Nash equilibria for convex games, arXiv:2310.04176v4, Remark 4.5, p.9

import Mathlib
import Definitions.Def_ApproxNashSet_Model

open scoped Pointwise

namespace ApproxNashSet

/-- **Remark 4.5 — the other players' strategies lie in the hull of the step-1 points.**
Feinstein–Hey–Rudloff, arXiv:2310.04176v4, Remark 4.5, p.9: "Since for any vertex x̄ of X, we have,
due to (12), (x̄−i, −x̄−i, fi(x̄)) ∈ PIn_i, we conclude that for any x ∈ X it holds
x−i ∈ conv{x1−i, ..., xs−i}."

If `X = conv V` and `V ⊆ G` (this is (12) for `G = X̄`), then for every player `i` and every
`x ∈ X`, `x₋ᵢ ∈ conv{z₋ᵢ | z ∈ G}`.

**Formalization Note.** Stated for any set `G` containing the generators (the paper's `G` is the
finite set `X̄ = {x¹, …, xˢ}` of step 1). -/
theorem remark_4_5 {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
    (X : Set (Joint n)) (V G : Set (Joint n)) (hX : X = convexHull ℝ V) (hVG : V ⊆ G)
    (i : ι) (x : Joint n) (hx : x ∈ X) :
    minus n i x ∈ convexHull ℝ (minus n i '' G) := by sorry

end ApproxNashSet
