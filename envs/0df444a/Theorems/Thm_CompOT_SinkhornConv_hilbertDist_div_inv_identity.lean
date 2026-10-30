-- Prove2me | Theorems.Thm_CompOT_SinkhornConv_hilbertDist_div_inv_identity
-- name    : CompOT.SinkhornConv.hilbertDist_div_inv_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:22:27.859166+00:00
-- url     : https://prove2.me/theorems/74fcda72-a1d9-4951-bc8f-5fb860423b7e
-- title:
--   Proof of Theorem 4.2: $d_{\mathcal H}(v,v') = d_{\mathcal H}(v/v', \mathbb 1_m) = d_{\mathcal H}(\mathbb 1_m/v, \mathbb 1_m/v')$
-- statement:
--   For all vectors $v, v'\in\mathbb R^m$ with positive entries,
--   $$d_{\mathcal H}(v,v') = d_{\mathcal H}(v/v', \mathbb 1_m) = d_{\mathcal H}(\mathbb 1_m/v, \mathbb 1_m/v'),$$
--   where the divisions are entrywise and $\mathbb 1_m$ is the all-ones vector.
--
--   The second identity shows that entrywise inversion is an isometry of the Hilbert metric; in the convergence proof it turns $d_{\mathcal H}(a/(Kv^{(\ell)}), a/(Kv^\star))$ into $d_{\mathcal H}(Kv^{(\ell)}, Kv^\star)$, to which Birkhoff's theorem applies.
--
--   Differences from the source: none.
-- source:
--   Peyré, Cuturi, Computational Optimal Transport, Found. Trends Mach. Learn. 11(5–6) (2019), doi:10.1561/2200000073, §4.2, proof of Theorem 4.2, unnumbered display, p. 441

import Mathlib
import Definitions.Def_CompOT_SinkhornConv_hilbertDist

open Matrix

namespace CompOT.SinkhornConv

/-- **Invariances of `d_H`: `d_H(v, v') = d_H(v/v', 1_m) = d_H(1_m/v, 1_m/v')`.**
Peyré, Cuturi, *Computational Optimal Transport*, Found. Trends Mach. Learn. 11(5–6) (2019), §4.2, proof of Theorem 4.2, unnumbered display, p. 441: "One notices that for any
(v, v′) ∈ (Rm+,∗)², one has dH(v, v′) = dH(v/v′, 1m) = dH(1m/v, 1m/v′)."

For all positive `v, v' ∈ ℝᵐ`, with entrywise division,
`d_H(v, v') = d_H(v/v', 1_m)` and `d_H(v/v', 1_m) = d_H(1_m/v, 1_m/v')`.

**Formalization Note.** `/` on `Fin m → ℝ` is entrywise and `1` is the all-ones vector `1_m`. -/
theorem hilbertDist_div_inv_identity {m : ℕ} (v v' : Fin m → ℝ)
    (hv : ∀ k, 0 < v k) (hv' : ∀ k, 0 < v' k) :
    hilbertDist v v' = hilbertDist (v / v') 1 ∧
      hilbertDist (v / v') 1 = hilbertDist (1 / v) (1 / v') := by sorry

end CompOT.SinkhornConv
