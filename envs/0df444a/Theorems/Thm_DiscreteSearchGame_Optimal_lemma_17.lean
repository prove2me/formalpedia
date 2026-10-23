-- Prove2me | Theorems.Thm_DiscreteSearchGame_Optimal_lemma_17
-- name    : DiscreteSearchGame.Optimal.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:43.593598+00:00
-- url     : https://prove2.me/theorems/cddd81b8-ea3f-4680-8280-c7eaa947d48f
-- title:
--   Lemma 17, p. 44 — at a tie point p ∈ 𝒫(ε), f(r, x_a) → f(r, p) along x_a → p in 𝒫(p, Σ) when all elements of r lie in Σ
-- statement:
--   Let $\epsilon\in(0,1/n)$ and let $p\in\mathcal P(\epsilon)$ be a tie point, i.e. there are at least two Gittins search sequences against $p$. Let $\Sigma\subseteq S_n$ and let $(x_a)_{a\ge1}$ be a sequence in
--   $$\mathcal P(p,\Sigma)=\Big\{x\in\mathcal P:\ \frac{x_{\sigma(i)}}{p_{\sigma(i)}}\ge\frac{x_{\sigma(i+1)}}{p_{\sigma(i+1)}},\ i=1,\dots,n-1,\ \sigma\in\Sigma\Big\}$$
--   with $x_a\to p$. Then for every tie-breaking rule $r\in\mathcal R$ all of whose elements belong to $\Sigma$,
--   $$\lim_{a\to\infty} f(r,x_a)=f(r,p).$$
--
--   It controls the limit of payoff vectors along sequences of hiding strategies approaching a tie point from a region where the tie is resolved consistently with the rule.
--
--   **Formalization Note.** $\sigma(i)$ is the box in position $i$ of $\sigma$ (`σ : Equiv.Perm (Fin n)` read as position ↦ box); `Sig` is a set of permutations. Limits are in `ℝ≥0∞`ⁿ. Rules are indexed by search step, as in Lemma 16.
-- source:
--   Clarkson, Lin & Glazebrook, A Classical Search Game in Discrete Locations, arXiv:2103.09310v1, p. 44, Lemma 17 and (33)

import Mathlib
import Definitions.Def_AllocationIndices_Jobs
import Definitions.Def_DiscreteSearchGame_Optimal_Model

open AllocationIndices Filter Topology

namespace DiscreteSearchGame.Optimal

/-- Lemma 17, p. 44: at a tie point `p ∈ 𝒫(ε)`, for `Σ ⊆ Sₙ`, a sequence `x_a → p` in `𝒫(p, Σ)`
and a rule `r` all of whose orderings lie in `Σ`, `f(r, x_a) → f(r, p)`. -/
theorem lemma_17 {n : ℕ} [NeZero n] (t q : Fin n → ℝ) (ht : ∀ i, 0 < t i) (hq0 : ∀ i, 0 < q i)
    (hq1 : ∀ i, q i < 1)
    (ε : ℝ) (hε : 0 < ε) (hεn : ε < 1 / (n : ℝ)) (p : Fin n → ℝ) (hp : p ∈ interiorEps ε)
    (htie : IsTiePoint t q p) (Sig : Set (Equiv.Perm (Fin n))) (x : ℕ → Fin n → ℝ)
    (hx : ∀ a, x a ∈ orderCone p Sig) (hlim : Tendsto x atTop (𝓝 p))
    (r : Rule n) (hr : ∀ k, r k ∈ Sig) :
    Tendsto (fun a => ruleVec t q r (x a)) atTop (𝓝 (ruleVec t q r p)) := by sorry

end DiscreteSearchGame.Optimal
