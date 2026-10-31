-- Prove2me | Theorems.Thm_ApproxNashSet_exists_minimal_on_fibre
-- name    : ApproxNashSet.exists_minimal_on_fibre
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:17:47.767009+00:00
-- url     : https://prove2.me/theorems/784d604b-546b-4da7-bb01-6731e14b21e9
-- title:
--   Proof of Lemma 4.10 — above every point $(a,-a,t)$ of $P^{In}_i$ there is a minimal element $(a,-a,\hat y)$
-- statement:
--   Let $G=\{x^1,\dots,x^s\}$ be a finite set of joint strategies, let $f_i$ be any cost, and let
--   $$P^{In}_i=\operatorname{conv}\{(x_{-i},-x_{-i},f_i(x)):x\in G\}+\mathbb R^{m_i}_+ .$$
--   If $(a,-a,t)\in P^{In}_i$ for some $a\in\prod_{j\ne i}X_j$ and $t\in\mathbb R$, then there is $\hat y\in\mathbb R$ such that $(a,-a,\hat y)$ is a minimal element of $P^{In}_i$ (componentwise order).
--
--   In the proof of Lemma 4.10 this is applied with $a=x^*_{-i}$ for a Pareto optimal $x^*$; the minimal point is then covered by a maximal efficient face.
--
--   Differences from the source:
--   - generalization: a = x*₋ᵢ for a Pareto optimal x* and the step-1 set X̄ ⊆ X, f convex → any a with (a, −a, t) ∈ P^In_i(G), any finite G, any f; reason: the page's situation is an instance; the claim uses only finiteness of G
--   - generalization: N ≥ 2 players → any finite player type; reason: the statement concerns one player i and uses nothing about the others' number; N ≥ 2 is a special case
--   - encoding: objective space ℝ^{mᵢ} with ordering cone ℝ^{mᵢ}₊, strategy spaces Xᵢ = ℝ^{nᵢ}, players 1, …, N → Obj n i = (∏_{j≠i} ℝ^{nⱼ}) × (∏_{j≠i} ℝ^{nⱼ}) × ℝ with the componentwise order, Fin (n i) → ℝ, a finite type ι; reason: Lean convention; the same instances
-- source:
--   Feinstein–Hey–Rudloff, Approximating the set of Nash equilibria for convex games, arXiv:2310.04176v4, proof of Lemma 4.10, sentence "Then there is ŷ such that (x∗−i, −x∗−i, ŷ) is minimal in PIn_i", p.11

import Mathlib
import Definitions.Def_ApproxNashSet_Model

open scoped Pointwise

namespace ApproxNashSet

/-- **A minimal point of `PIn_i` above every fibre point.**
Feinstein–Hey–Rudloff, arXiv:2310.04176v4, proof of Lemma 4.10, p.11: "Then there is ŷ such that
(x∗−i, −x∗−i, ŷ) is minimal in PIn_i".

Let `G` be a finite set of joint strategies and `PIn_i(G) = conv{gᵢ(x) | x ∈ G} + ℝ^{mᵢ}₊`. If
`(a, −a, t) ∈ PIn_i(G)` for some `a ∈ ∏_{j≠i} ℝ^{nⱼ}` and `t ∈ ℝ`, then there is `ŷ ∈ ℝ` such that
`(a, −a, ŷ)` is a minimal element of `PIn_i(G)`.

**Formalization Note.** `G` is a `Finset` (the paper's `X̄ = {x¹, …, xˢ}`); no assumption on `f`. -/
theorem exists_minimal_on_fibre {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
    (f : ι → Joint n → ℝ) (i : ι) (G : Finset (Joint n)) (a : OthersStrat n i) (t : ℝ)
    (ht : ((a, -a, t) : Obj n i) ∈ PIn (g n f i) (↑G : Set (Joint n))) :
    ∃ yhat : ℝ, ((a, -a, yhat) : Obj n i) ∈ MinSet (PIn (g n f i) (↑G : Set (Joint n))) := by sorry

end ApproxNashSet
