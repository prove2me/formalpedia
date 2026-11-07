-- Prove2me | Theorems.Thm_ArbSlowFP_eq_4
-- name    : ArbSlowFP.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:46:28.874793+00:00
-- url     : https://prove2.me/theorems/41f501e2-93a2-4d59-8f5c-01708318ae23
-- title:
--   (4) — for skew-symmetric $A$, $\mathrm{Gap}_A(z/t,z/t)=\frac2t\max_i(Az)_i$
-- statement:
--   Let $A$ be a real skew-symmetric matrix on a nonempty finite action set, let $z$ be a real vector and let $t\ge1$ be an integer. Then
--   $$\mathrm{Gap}_A(z/t,z/t)=\frac2t\max_i(Az)_i .$$
--   This converts the duality gap of a synchronized run into the height of its score vector.
--
--   **Formalization Note** The paper states this for the common count vector $z_t$ of a synchronized run; every such vector is covered.
--
--   Differences from the source:
--   - generalization: z_t the common count vector of a synchronized run → an arbitrary real vector z; reason: the identity uses only skew-symmetry, and z_t is one such vector
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), p.2, eq. (4)

import Mathlib
import Definitions.Def_ArbSlowFP_IsFPRun

open Matrix

namespace ArbSlowFP

/-- Eq. (4), p.2 (arXiv:2610.08768, version of November 3, 2026, sha256 977c34b6…): for skew-symmetric
`A` and `t ≥ 1`, `Gap_A(z_t/t, z_t/t) = (2/t) max_i (Az_t)_i`.

**Formalization Note.** Stated for an arbitrary real vector `z` on a nonempty finite action type,
which covers every count vector of a synchronized run. -/
theorem eq_4 {ι : Type*} [Fintype ι] [Nonempty ι] (A : Matrix ι ι ℝ) (hA : Aᵀ = -A)
    (z : ι → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    gap A (fun a => z a / (t : ℝ)) (fun a => z a / (t : ℝ)) = 2 / (t : ℝ) * ⨆ i, (A *ᵥ z) i := by sorry

end ArbSlowFP
