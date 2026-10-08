-- Prove2me | Theorems.Thm_CompOT_Sinkhorn_thm_4_2_proof_one_step
-- name    : CompOT.Sinkhorn.thm_4_2_proof_one_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:10.04014+00:00
-- url     : https://prove2.me/theorems/1c5d6527-eb36-4d34-9734-2728158570d7
-- title:
--   §4.2, proof of Theorem 4.2, p. 442 — d_H(u^(ℓ+1), u⋆) = d_H(Kv^(ℓ), Kv⋆) ≤ λ(K) d_H(v^(ℓ), v⋆), and the v-analogue
-- statement:
--   Let $n, m \ge 1$, let $K \in \mathbb{R}^{n\times m}$, $a \in \mathbb{R}^n$, $b \in \mathbb{R}^m$ have positive entries, let $(u^{(\ell)}, v^{(\ell)})$ be a run of Sinkhorn's algorithm
--   $$v^{(0)} = \mathbb{1}_m,\qquad u^{(\ell+1)} = \frac{a}{Kv^{(\ell)}},\qquad v^{(\ell+1)} = \frac{b}{K^\top u^{(\ell+1)}},$$
--   and let $(u^\star, v^\star)$ be a pair of vectors with positive entries solving the scaling equations $u^\star \odot (Kv^\star) = a$, $v^\star \odot (K^\top u^\star) = b$. Then for every $\ell \ge 0$,
--   $$d_{\mathcal H}(u^{(\ell+1)}, u^\star) = d_{\mathcal H}(Kv^{(\ell)}, Kv^\star) \le \lambda(K)\, d_{\mathcal H}(v^{(\ell)}, v^\star), \qquad d_{\mathcal H}(v^{(\ell+1)}, v^\star) \le \lambda(K)\, d_{\mathcal H}(u^{(\ell+1)}, u^\star).$$
--
--   Each half-step of Sinkhorn's algorithm contracts the distance to the fixed point by the Birkhoff factor $\lambda(K)$, so a full iteration contracts it by $\lambda(K)^2$.
--
--   **Formalization Note** The book displays the $u$-update; the $v$-update bound is its mirror image (with $K^\top$ in place of $K$; $\lambda(K^\top) = \lambda(K)$), which the proof uses implicitly to obtain the factor $\lambda(K)^2$ in the next display. Indices are $0$-based.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), §4.2, Remark 4.14, proof of Theorem 4.2, first display, p. 442

import Mathlib
import Definitions.Def_CompOT_Sinkhorn_Defs

namespace CompOT.Sinkhorn

open Matrix

/-- Proof of Theorem 4.2, p. 442 (first display): for a Sinkhorn run (4.15) and a positive
solution `(u⋆, v⋆)` of (4.14), every half-step contracts by `λ(K)`:
`d_H(u^{(ℓ+1)}, u⋆) = d_H(K v^{(ℓ)}, K v⋆) ≤ λ(K) d_H(v^{(ℓ)}, v⋆)`, and (the analogue for
the `v`-update) `d_H(v^{(ℓ+1)}, v⋆) ≤ λ(K) d_H(u^{(ℓ+1)}, u⋆)`. -/
theorem thm_4_2_proof_one_step {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (K : Matrix (Fin n) (Fin m) ℝ) (hK : ∀ i j, 0 < K i j)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (b : Fin m → ℝ) (hb : ∀ j, 0 < b j)
    (u : ℕ → Fin n → ℝ) (v : ℕ → Fin m → ℝ) (hrun : IsSinkhornRun K a b u v)
    (us : Fin n → ℝ) (vs : Fin m → ℝ) (hus : ∀ i, 0 < us i) (hvs : ∀ j, 0 < vs j)
    (hsol : IsScalingSolution K a b us vs) :
    ∀ ℓ : ℕ,
      hilbertMetric (u (ℓ + 1)) us = hilbertMetric (K *ᵥ v ℓ) (K *ᵥ vs) ∧
      hilbertMetric (u (ℓ + 1)) us ≤ lam K * hilbertMetric (v ℓ) vs ∧
      hilbertMetric (v (ℓ + 1)) vs ≤ lam K * hilbertMetric (u (ℓ + 1)) us := by sorry

end CompOT.Sinkhorn
