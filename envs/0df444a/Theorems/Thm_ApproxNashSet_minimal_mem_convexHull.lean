-- Prove2me | Theorems.Thm_ApproxNashSet_minimal_mem_convexHull
-- name    : ApproxNashSet.minimal_mem_convexHull
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:17:49.678057+00:00
-- url     : https://prove2.me/theorems/a57dfbdb-dedd-4bda-9afc-fdab4b2eedfd
-- title:
--   Proof of Lemma 4.10 — minimal elements of $\mathrm{conv}\,S+\mathbb R^{m_i}_+$ lie in $\mathrm{conv}\,S$
-- statement:
--   Let $S$ be any subset of the objective space $\mathbb R^{m_i}$ of problem (3), ordered componentwise. Every minimal element of $\operatorname{conv}S+\mathbb R^{m_i}_+$ belongs to $\operatorname{conv}S$:
--   $$\operatorname{Min}\bigl(\operatorname{conv}S+\mathbb R^{m_i}_+\bigr)\subseteq\operatorname{conv}S .$$
--
--   With $S=g_i[\bar{\mathcal X}]$ this is the step of the proof of Lemma 4.10 that writes the minimal point $(x^*_{-i},-x^*_{-i},\hat y)$ as a convex combination $\sum_l\hat\lambda^l g_i(x^l)$.
--
--   Differences from the source:
--   - generalization: S = gᵢ[X̄] = {(x−i, −x−i, fi(x)) | x ∈ X̄} → any S ⊆ Obj n i; reason: the page's S is an instance; the claim uses only the shape conv S + ℝ^{mᵢ}₊
--   - generalization: N ≥ 2 players → any finite player type; reason: the statement concerns one player i and uses nothing about the others' number; N ≥ 2 is a special case
--   - encoding: objective space ℝ^{mᵢ} with ordering cone ℝ^{mᵢ}₊, strategy spaces Xᵢ = ℝ^{nᵢ}, players 1, …, N → Obj n i = (∏_{j≠i} ℝ^{nⱼ}) × (∏_{j≠i} ℝ^{nⱼ}) × ℝ with the componentwise order, Fin (n i) → ℝ, a finite type ι; reason: Lean convention; the same instances
-- source:
--   Feinstein–Hey–Rudloff, Approximating the set of Nash equilibria for convex games, arXiv:2310.04176v4, proof of Lemma 4.10, sentence "So there are λ̂1, ..., λ̂s ≥ 0 …", p.11

import Mathlib
import Definitions.Def_ApproxNashSet_Model

open scoped Pointwise

namespace ApproxNashSet

/-- **Minimal points of `conv S + ℝ^{mᵢ}₊` lie in `conv S`.**
Feinstein–Hey–Rudloff, arXiv:2310.04176v4, proof of Lemma 4.10, p.11: "So there are
λ̂1, ..., λ̂s ≥ 0 with Σ_{l=1}^s λ̂l = 1 such that (x∗−i, −x∗−i, ŷ) = (Σ λ̂l xl−i, −Σ λ̂l xl−i,
Σ λ̂l fi(xl))", i.e. the minimal element `(x*₋ᵢ, −x*₋ᵢ, ŷ)` of `PIn_i` is a convex combination of
the generating images.

For every set `S` in the objective space `ℝ^{mᵢ}` of problem (3), every minimal element of
`conv S + ℝ^{mᵢ}₊` belongs to `conv S`.

**Formalization Note.** Stated for any set `S ⊆ Obj n i` (the paper's `S` is `gᵢ[X̄]`). -/
theorem minimal_mem_convexHull {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} (i : ι)
    (S : Set (Obj n i)) :
    MinSet (convexHull ℝ S + {d : Obj n i | 0 ≤ d}) ⊆ convexHull ℝ S := by sorry

end ApproxNashSet
