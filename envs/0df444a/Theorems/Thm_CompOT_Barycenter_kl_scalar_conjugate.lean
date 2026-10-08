-- Prove2me | Theorems.Thm_CompOT_Barycenter_kl_scalar_conjugate
-- name    : CompOT.Barycenter.kl_scalar_conjugate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:34:09.806992+00:00
-- url     : https://prove2.me/theorems/4caec703-04d3-4102-9190-a1d4f01add41
-- title:
--   Proof of Proposition 9.1, p. 530 — scalar KL conjugate
-- statement:
--   Let $k>0$ and $u\in\mathbb R$. For nonnegative $r$, define $\mathrm{KL}(r\mid k)=r\log(r/k)-r+k$, with the value $k$ at $r=0$. Then
--   $$\max_{r\ge0}\{ur-\mathrm{KL}(r\mid k)\}=k(e^u-1),$$
--   and the maximum is attained at $r=ke^u$.
--
--   This scalar identity is the entrywise component of the matrix KL conjugate used in the barycenter dual program.
--
--   **Formalization Note** The printed domain $(u,k)\in\mathbb R_+^2$ is corrected to $u\in\mathbb R$, $k>0$, since the dual potential $u$ has no sign restriction.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), proof of Proposition 9.1 and (9.22), p. 530

import Mathlib
import Definitions.Def_CompOT_Barycenter_Defs

namespace CompOT.Barycenter

/-- Scalar part of (9.22), proof of Proposition 9.1, p. 530. -/
theorem kl_scalar_conjugate (u k : ℝ) (hk : 0 < k) :
    (∀ r : ℝ, 0 ≤ r → u * r - klEntry r k ≤ k * (Real.exp u - 1)) ∧
    0 ≤ k * Real.exp u ∧
    u * (k * Real.exp u) - klEntry (k * Real.exp u) k =
      k * (Real.exp u - 1) := by sorry

end CompOT.Barycenter
