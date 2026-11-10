-- Prove2me | Theorems.Thm_AgnosticImitate_Reduction_lemma_3_3
-- name    : AgnosticImitate.Reduction.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T21:23:57.116727+00:00
-- url     : https://prove2.me/theorems/53c4efb7-c45a-4d81-bb35-05cc43a11b26
-- title:
--   Lemma 3.3 — ∂ℓ ∘ k is a superderivative of the entropy, and D_ℓ(p, k(q)) is the Bregman divergence D_{h_ℓ}(p, q)
-- statement:
--   Let $\ell$ be a loss with actions in $A$ and let $k$ be a best-response function of $\ell$ on $[\pm1]$. Then $h'_\ell=\partial\ell\circ k$ is a superderivative of the entropy $h_\ell(p)=\inf_a\ell(p,a)$ on $[\pm1]$:
--   $$h_\ell(y)\le h_\ell(x)+h'_\ell(x)(y-x)\qquad(x,y\in[-1,1]),$$
--   and for all $p,q\in[-1,1]$
--   $$D_\ell(p,k(q))=D_{h_\ell}(p,q)=h_\ell(q)+h'_\ell(q)(p-q)-h_\ell(p),$$
--   the Bregman divergence from $p$ to $q$ with respect to $h_\ell$ and the superderivative $h'_\ell$.
--
--   Differences from the source:
--   - encoding: a loss ℓ : {±1} × A → ℝ → ℓ : ℝ → A → ℝ, used only at y = 1 and y = −1 (expLoss); reason: the values at other y never enter
--   - encoding: k_ℓ(p) ∈ argmin_a ℓ(p, a), the best-response function → a given selection k with IsBestResponse ℓ k (ℓ(p, k(p)) ≤ ℓ(p, a) for all p ∈ [−1, 1] and all a); reason: the paper's k_ℓ is a chosen selection; a best response need not exist in general, so it is assumed given
--   - reading: superderivative: h(y) ≤ h(x) + h'(x)(y − x) for all x, y ∈ ℝ (Definition 2.1) → for all x, y ∈ [−1, 1] (IsSuperderivative); reason: h_ℓ and k_ℓ are defined for p ∈ [±1] (Definition 2.4, Lemma 3.4's means lie in [±1])
--   - encoding: D_{h_ℓ}, the Bregman divergence with respect to h_ℓ, h'_ℓ (Definition 2.2, footnote 7) → bregmanConcave h h' p q = h(q) + h'(q)(p − q) − h(p), i.e. D_{−h}(p, q) with subderivative −h'; reason: Definition 2.2 applied to the convex −h_ℓ, as the paper's 'D_h instead of D_{−h}' convention says
--   - encoding: h_ℓ(p) = inf_a ℓ(p, a) → the real infimum ⨅ a, expLoss ℓ p a; reason: for p ∈ [−1, 1] the set is bounded below and the infimum is attained at k(p), so it is the paper's value
-- source:
--   Casacuberta, Gopalan, Kanade, Reingold, Stavropoulos, Tankala (2026), Agnostic Learning by Imitating, STOC 2027 submission, SHA-256 225d86c2…0fb04, Lemma 3.3, p. 20 (PDF 22); proof p. 40 (PDF 42)

import Mathlib
import Definitions.Def_AgnosticImitate_Reduction_Losses

namespace AgnosticImitate.Reduction

/-- Lemma 3.3 (p. 20, PDF 22). If `k` is a best-response function of `ℓ`, then
`h'_ℓ = ∂ℓ ∘ k` is a superderivative of the entropy `h_ℓ` on `[±1]`, and
`D_ℓ(p, k(q)) = D_{h_ℓ}(p, q)` for all `p, q ∈ [±1]`, the Bregman divergence being taken with
respect to `h_ℓ` and the superderivative `h'_ℓ`. -/
theorem lemma_3_3 {A : Type*} (ℓ : ℝ → A → ℝ) (k : ℝ → A) (hk : IsBestResponse ℓ k) :
    IsSuperderivative (entropy ℓ) (fun q => discDeriv ℓ (k q)) ∧
    ∀ p ∈ Set.Icc (-1 : ℝ) 1, ∀ q ∈ Set.Icc (-1 : ℝ) 1,
      divergence ℓ p (k q) = bregmanConcave (entropy ℓ) (fun q => discDeriv ℓ (k q)) p q := by sorry

end AgnosticImitate.Reduction
