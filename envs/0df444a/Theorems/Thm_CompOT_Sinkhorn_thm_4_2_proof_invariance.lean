-- Prove2me | Theorems.Thm_CompOT_Sinkhorn_thm_4_2_proof_invariance
-- name    : CompOT.Sinkhorn.thm_4_2_proof_invariance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:03.878986+00:00
-- url     : https://prove2.me/theorems/c35e0934-5f9d-43d2-b137-b335d5e70c2f
-- title:
--   §4.2, proof of Theorem 4.2, pp. 441–442 — d_H(v, v′) = d_H(v/v′, 𝟙) = d_H(𝟙/v, 𝟙/v′) and d_H(c⊙v, c⊙v′) = d_H(v, v′)
-- statement:
--   Let $m \ge 1$ and let $v, v' \in \mathbb{R}^m$ have positive entries. Then
--   $$d_{\mathcal H}(v,v') = d_{\mathcal H}(v/v', \mathbb{1}_m) = d_{\mathcal H}(\mathbb{1}_m/v, \mathbb{1}_m/v'),$$
--   and for every $c \in \mathbb{R}^m$ with positive entries,
--   $$d_{\mathcal H}(c \odot v, c \odot v') = d_{\mathcal H}(v, v'),$$
--   where products and quotients of vectors are entrywise.
--
--   These invariances of Hilbert's projective metric under entrywise division, inversion and positive diagonal scaling are what reduce one Sinkhorn update $u \mapsto a/(Kv)$ to an application of the matrix $K$.
--
--   **Formalization Note** The first display is the opening of the proof (p. 441). The diagonal scaling invariance is not displayed on its own in the book; it is the step used in the first equality $d_{\mathcal H}(a/(Kv^{(\ell)}), a/(Kv^\star)) = d_{\mathcal H}(Kv^{(\ell)}, Kv^\star)$ of the next display (p. 442), and it is cited to that display.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), §4.2, Remark 4.14, proof of Theorem 4.2, first display, p. 441, and first equality of the first display on p. 442

import Mathlib
import Definitions.Def_CompOT_Sinkhorn_Defs

namespace CompOT.Sinkhorn

/-- Proof of Theorem 4.2, p. 441 (first display) and p. 442 (first equality of the first
display): for positive `v, v'`,
`d_H(v, v') = d_H(v/v', 𝟙_m) = d_H(𝟙_m/v, 𝟙_m/v')`, and `d_H` is invariant under
entrywise multiplication of both arguments by a positive vector `c`. -/
theorem thm_4_2_proof_invariance {m : ℕ} (hm : 0 < m) (v v' : Fin m → ℝ)
    (hv : ∀ j, 0 < v j) (hv' : ∀ j, 0 < v' j) :
    hilbertMetric v v' = hilbertMetric (v / v') 1 ∧
    hilbertMetric v v' = hilbertMetric (1 / v) (1 / v') ∧
    ∀ c : Fin m → ℝ, (∀ j, 0 < c j) → hilbertMetric (c * v) (c * v') = hilbertMetric v v' := by sorry

end CompOT.Sinkhorn
