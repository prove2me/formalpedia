-- Prove2me | Theorems.Thm_FamousTheorems_polarization_identity_7a
-- name    : FamousTheorems.polarization_identity_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:25:51.814733+00:00
-- url     : https://prove2.me/theorems/f1744b54-274c-452f-9712-a48d9d11bb4e
-- title:
--   The polarization identity
-- statement:
--   **The polarization identity.** Let $E$ be an inner product space over $\mathbb K=\mathbb R$ or $\mathbb C$, with inner product conjugate-linear in the first argument. For all $x,y\in E$,
--   $$\langle x,y\rangle=\frac{\|x+y\|^2-\|x-y\|^2+\big(\|x-iy\|^2-\|x+iy\|^2\big)\,i}{4}.$$
--   Over $\mathbb R$, where $i=0$, this reduces to $\langle x,y\rangle=\frac14\big(\|x+y\|^2-\|x-y\|^2\big)$.
--
--   The identity recovers the inner product from the norm. Hence linear maps that preserve norms also preserve inner products. Together with the parallelogram law it characterises the norms that come from inner products.
--
--   **Formalization note.** Mathlib's `inner_eq_sum_norm_sq_div_four`. `RCLike 𝕜` covers $\mathbb R$ and $\mathbb C$, `RCLike.I` is the imaginary unit of $\mathbb K$ (equal to $0$ when $\mathbb K=\mathbb R$), and the norms are cast into $\mathbb K$. Mathlib's inner product is conjugate-linear in the first argument.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `inner_eq_sum_norm_sq_div_four`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem polarization_identity_7a {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] (x y : E) :
    inner 𝕜 x y = ((‖x + y‖ : 𝕜) ^ 2 - (‖x - y‖ : 𝕜) ^ 2 +
      ((‖x - (RCLike.I : 𝕜) • y‖ : 𝕜) ^ 2 - (‖x + (RCLike.I : 𝕜) • y‖ : 𝕜) ^ 2) * RCLike.I) / 4 := by sorry

end FamousTheorems
