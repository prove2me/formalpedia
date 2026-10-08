-- Prove2me | Theorems.Thm_CompOT_Sinkhorn_thm_4_2_proof_eq_4_23_display
-- name    : CompOT.Sinkhorn.thm_4_2_proof_eq_4_23_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:11.532842+00:00
-- url     : https://prove2.me/theorems/07b77a1a-9790-4718-94f5-fc66ff96a2df
-- title:
--   §4.2, proof of Theorem 4.2, p. 442 — d_H(u^(ℓ), u⋆) ≤ d_H(a, u^(ℓ) ⊙ (Kv^(ℓ))) + λ(K)² d_H(u^(ℓ), u⋆), and the v-analogue
-- statement:
--   In the setting of Sinkhorn's algorithm (positive $K$, $a$, $b$; a run $(u^{(\ell)}, v^{(\ell)})$ of (4.15) started at $v^{(0)} = \mathbb{1}_m$; a positive solution $(u^\star, v^\star)$ of the scaling equations (4.14)), with $\lambda(K)$ the Birkhoff contraction ratio:
--
--   1. for every $\ell \ge 1$,
--   $$d_{\mathcal H}(u^{(\ell)}, u^\star) \le d_{\mathcal H}\big(a,\ u^{(\ell)} \odot (Kv^{(\ell)})\big) + \lambda(K)^2\, d_{\mathcal H}(u^{(\ell)}, u^\star);$$
--   2. for every $\ell \ge 0$,
--   $$d_{\mathcal H}(v^{(\ell)}, v^\star) \le d_{\mathcal H}\big(b,\ v^{(\ell)} \odot (K^\top u^{(\ell+1)})\big) + \lambda(K)^2\, d_{\mathcal H}(v^{(\ell)}, v^\star).$$
--
--   Rearranged, these give the a posteriori error bounds (4.23): the distance of the current scaling to the solution is controlled by how far the current coupling is from satisfying the marginal constraints.
--
--   **Formalization Note** The $u$-statement is written for $u^{(\ell+1)}$, $\ell \ge 0$, since $u^{(0)}$ is not an iterate of (4.15). The $v$-statement is the book's "the second one being similar", with the mirrored argument: the marginal it uses is $v^{(\ell)} \odot (K^\top u^{(\ell+1)})$, the column sums of $\mathrm{diag}(u^{(\ell+1)})K\,\mathrm{diag}(v^{(\ell)})$, not those of $P^{(\ell)}$ (see the goal theorem).
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), §4.2, Remark 4.14, proof of Theorem 4.2, second display, p. 442

import Mathlib
import Definitions.Def_CompOT_Sinkhorn_Defs

namespace CompOT.Sinkhorn

open Matrix

/-- Proof of Theorem 4.2, p. 442 (second display): for every iterate `u^{(ℓ)}` with
`ℓ ≥ 1` (written `u (ℓ+1)`),
`d_H(u^{(ℓ)}, u⋆) ≤ d_H(a, u^{(ℓ)} ⊙ (K v^{(ℓ)})) + λ(K)² d_H(u^{(ℓ)}, u⋆)`,
and (the mirrored "second one", for every `ℓ ≥ 0`)
`d_H(v^{(ℓ)}, v⋆) ≤ d_H(b, v^{(ℓ)} ⊙ (Kᵀ u^{(ℓ+1)})) + λ(K)² d_H(v^{(ℓ)}, v⋆)`. -/
theorem thm_4_2_proof_eq_4_23_display {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (K : Matrix (Fin n) (Fin m) ℝ) (hK : ∀ i j, 0 < K i j)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (b : Fin m → ℝ) (hb : ∀ j, 0 < b j)
    (u : ℕ → Fin n → ℝ) (v : ℕ → Fin m → ℝ) (hrun : IsSinkhornRun K a b u v)
    (us : Fin n → ℝ) (vs : Fin m → ℝ) (hus : ∀ i, 0 < us i) (hvs : ∀ j, 0 < vs j)
    (hsol : IsScalingSolution K a b us vs) :
    (∀ ℓ : ℕ, hilbertMetric (u (ℓ + 1)) us ≤
      hilbertMetric a (u (ℓ + 1) * (K *ᵥ v (ℓ + 1))) +
        lam K ^ 2 * hilbertMetric (u (ℓ + 1)) us) ∧
    (∀ ℓ : ℕ, hilbertMetric (v ℓ) vs ≤
      hilbertMetric b (v ℓ * (Kᵀ *ᵥ u (ℓ + 1))) +
        lam K ^ 2 * hilbertMetric (v ℓ) vs) := by sorry

end CompOT.Sinkhorn
