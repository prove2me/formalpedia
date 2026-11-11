-- Prove2me | Theorems.Thm_ContinualHardness_Linear_lemma_A_9
-- name    : ContinualHardness.Linear.lemma_A_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:11:11.726263+00:00
-- url     : https://prove2.me/theorems/541fa7be-ca0f-4d81-b17d-898d27db3d79
-- title:
--   Lemma A.9 — on a nice edge between good vertices the projected heavy-coordinate sets S0 intersect
-- statement:
--   Let $\pi_u,\pi_v:[M]\to[N]$ be the projections of an edge $e=(u,v)$ at its two endpoints, every preimage $\pi_u^{-1}(i)$, $\pi_v^{-1}(i)$ of size at most $q$, and let $\tau>0$. Let $a=r_{ut}$, $b=r_{vt}\in\mathbb R^M$ be blocks of a folded weight vector, i.e. (16)
--   $$\sum_{j\in\pi_u^{-1}(i)}a_j=\sum_{j\in\pi_v^{-1}(i)}b_j\qquad\text{for every }i\in[N],$$
--   and let both be **good** in the sense of (27): $|a_j|>\tau\|a\|_2$ for some $j$ and $|b_j|>\tau\|b\|_2$ for some $j$. With (28)–(29)
--   $$S_0(a)=\{j:|a_j|>\tfrac\tau4\|a\|_2\},\qquad S_1(a)=\{j\notin S_0(a):|a_j|>\tfrac{\tau}{4q}\|a\|_2\},$$
--   and likewise for $b$, let the edge be **nice**: $\pi_v$ is injective on $S_0(b)\cup S_1(b)$ and $\pi_u$ is injective on $S_0(a)\cup S_1(a)$. Then
--   $$\pi_v(S_0(b))\cap\pi_u(S_0(a))\ne\emptyset .$$
--   In the NO case of Theorem A.8 this makes the randomized labeling (a uniform label from $S_0$ at each good vertex) satisfy every nice edge between good vertices with probability at least $(\tau^2/16)^2$.
--
--   Differences from the source:
--   - generalization: a nice edge (u, v) of the reduction's Smooth-Label-Cover instance induced by good vertices, for the folded classifier r and q = 4^R → arbitrary maps π_u, π_v : [M] → [N] with preimages of size ≤ q (any q), any τ > 0, blocks a = r_{ut}, b = r_{vt} satisfying the folding identity (16), 'good' replaced by its consequence (27); reason: these are exactly the facts the proof uses; in the NO case every nice edge between good vertices satisfies them ((16) from r ∈ F, (27) from Lemma A.7, the preimage bound from Theorem A.3), so the lemma specializes to the printed one
--   - encoding: π^{e,v}(S0(v)) ∩ π^{e,u}(S0(u)) ≠ ∅ → ∃ i, (∃ j ∈ S0(b), π_v j = i) ∧ (∃ j ∈ S0(a), π_u j = i), with S0 and S0 ∪ S1 written as explicit threshold sets; reason: Lean representation of the images and of the sets (28)-(29)
-- source:
--   Saket, Intractability of Continual Learning using Parametric Models with Unlimited Replay Buffer, STOC 2027 submission (manuscript sha256 86821df1…), p. 24, Lemma A.9, with (16), (27)-(29) (PDF p. 25)

import Mathlib

namespace ContinualHardness.Linear

/-- Lemma A.9, p. 24, in self-contained form. Let `πu, πv : [M] → [N]` be the projections of an
edge `e = (u, v)` at its endpoints, every preimage of size at most `q`; let `a = r_{ut}` and
`b = r_{vt}` be blocks of a folded weight vector (for every `i ∈ [N]`,
`∑_{j ∈ πu⁻¹(i)} a_j = ∑_{j ∈ πv⁻¹(i)} b_j`, Eq. (16)), both good in the sense of (27) (some
coordinate exceeds `τ` times the block norm). With `S₀, S₁` as in (28), (29) and the edge nice
(`πv` injective on `S₀(v) ∪ S₁(v)`, `πu` injective on `S₀(u) ∪ S₁(u)`), the images
`πv(S₀(v))` and `πu(S₀(u))` intersect. -/
theorem lemma_A_9 (M N q : ℕ) (τ : ℝ) (hτ : 0 < τ)
    (πu πv : Fin M → Fin N)
    (hqu : ∀ i : Fin N, (Finset.univ.filter fun j => πu j = i).card ≤ q)
    (hqv : ∀ i : Fin N, (Finset.univ.filter fun j => πv j = i).card ≤ q)
    (a b : Fin M → ℝ)
    (hfold : ∀ i : Fin N,
      ∑ j ∈ Finset.univ.filter (fun j => πu j = i), a j =
        ∑ j ∈ Finset.univ.filter (fun j => πv j = i), b j)
    (hgood_u : ∃ j, τ * Real.sqrt (∑ k, a k ^ 2) < |a j|)
    (hgood_v : ∃ j, τ * Real.sqrt (∑ k, b k ^ 2) < |b j|)
    (hnice_u : Set.InjOn πu
      ({j | τ / 4 * Real.sqrt (∑ k, a k ^ 2) < |a j|} ∪
        {j | ¬ (τ / 4 * Real.sqrt (∑ k, a k ^ 2) < |a j|) ∧
          τ / (4 * q) * Real.sqrt (∑ k, a k ^ 2) < |a j|}))
    (hnice_v : Set.InjOn πv
      ({j | τ / 4 * Real.sqrt (∑ k, b k ^ 2) < |b j|} ∪
        {j | ¬ (τ / 4 * Real.sqrt (∑ k, b k ^ 2) < |b j|) ∧
          τ / (4 * q) * Real.sqrt (∑ k, b k ^ 2) < |b j|})) :
    ∃ i : Fin N,
      (∃ j, τ / 4 * Real.sqrt (∑ k, b k ^ 2) < |b j| ∧ πv j = i) ∧
      (∃ j, τ / 4 * Real.sqrt (∑ k, a k ^ 2) < |a j| ∧ πu j = i) := by sorry

end ContinualHardness.Linear
