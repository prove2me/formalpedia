-- Prove2me | Theorems.Thm_DynBrooks_lemma_4_5
-- name    : DynBrooks.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:06:34.145222+00:00
-- url     : https://prove2.me/theorems/18453300-e8cf-4073-900c-d74203d25637
-- title:
--   Lemma 4.5 — sparsity under edge additions
-- statement:
--   Let $F\subseteq J$ be graphs on the same finite vertex set, both of maximum degree at most $\Delta$. Suppose every edge of $J\setminus F$ has an endpoint of degree at most $\Delta-h$ in $J$, where $1\le h\le\Delta$. Then, for every vertex $u$,
--
--   $$\zeta_J(u)=\Omega\Bigl(\frac h\Delta\,\zeta_F(u)\Bigr),$$
--
--   that is, there is an absolute constant $c>0$ with $\zeta_J(u)\ge c\,(h/\Delta)\,\zeta_F(u)$.
--
--   This transfers sparsity from the graph of selected core vertices to the auxiliary graph $J$ in the proof of Lemma 4.3.
--
--   Differences from the source: none.
-- source:
--   Mishra, Mukherjee, Fully Dynamic Brooks Coloring (STOC 2027 submission, preprint, sha256 6542a9f18a48e0b539c2aadee984a641d38a01a551fd32d5fa4d4c5164e32d7b), Lemma 4.5, p.20 (PDF 22)

import Mathlib
import Definitions.Def_DynBrooks_Sparsity

namespace DynBrooks

open Classical in
/-- **Lemma 4.5** (Sparsity under edge additions; Mishra, Mukherjee, *Fully Dynamic Brooks Coloring*,
STOC 2027 submission, sha256 6542a9f1…, p.20 (PDF 22)). Let `F ⊆ J` be graphs on the same vertex set,
both of maximum degree at most `∆`. Suppose every edge of `J \ F` has an endpoint of degree at most
`∆ − h` in `J`, where `1 ≤ h ≤ ∆`. Then, for every vertex `u`, `ζ_J(u) = Ω((h/∆) ζ_F(u))`.

**Formalization Note.** The `Ω` constant `c > 0` is absolute: it is chosen before the vertex set, `∆`,
`h`, `F` and `J`. `ζ` is the real-valued sparsity of `DynBrooks.Sparsity`, relative to `∆`. -/
theorem lemma_4_5 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (V : Type) [Fintype V] (Δ h : ℕ) (F J : SimpleGraph V), F ≤ J →
        (∀ v, F.degree v ≤ Δ) → (∀ v, J.degree v ≤ Δ) → 1 ≤ h → h ≤ Δ →
        (∀ u v, J.Adj u v → ¬ F.Adj u v → J.degree u + h ≤ Δ ∨ J.degree v + h ≤ Δ) →
        ∀ u : V, c * ((h : ℝ) / Δ) * sparsity Δ F u ≤ sparsity Δ J u := by sorry

end DynBrooks
