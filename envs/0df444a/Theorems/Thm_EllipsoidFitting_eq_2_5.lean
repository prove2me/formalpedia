-- Prove2me | Theorems.Thm_EllipsoidFitting_eq_2_5
-- name    : EllipsoidFitting.eq_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:44:29.803308+00:00
-- url     : https://prove2.me/theorems/00dafe4b-e440-40b3-bdba-03d7477efbc7
-- title:
--   Eq. (2)–(5) — the decomposition $M=A+B$
-- statement:
--   For any points $v_1,\dots,v_m\in\mathbb R^d$, with $M[i,j]=\langle v_i,v_j\rangle^2$ and $A$, $B$, $M_\alpha$, $M_\beta$, $M_D$ as in eq. (2)–(5),
--   $$
--   M=A+B,\qquad A=\Bigl(1+\frac1d\Bigr)I_m+M_\alpha+M_\beta+M_D,\qquad B=\frac1dJ_m+\frac1d\bigl(\mathbf 1_m\eta^\top+\eta\mathbf 1_m^\top\bigr),
--   $$
--   and for $i\ne j$ the two expressions of (3) agree:
--   $$
--   \sum_{a\ne b\in[d]}v_i[a]v_i[b]v_j[a]v_j[b]=2\sum_{a<b\in[d]}v_i[a]v_i[b]v_j[a]v_j[b].
--   $$
--
--   The identity is deterministic. It splits $M$ into a Wishart-like part $A$ and a perturbation $B$ of rank at most two.
--
--   **Formalization Note** $M$ is the entrywise formula for $LL^*$ (`gram`).
--
--   Differences from the source:
--   - encoding: M_α and M_β are off-diagonal, M_D is diagonal → entries not given by (3)–(5) are 0; reason: as stated on p.17
--   - encoding: M := LL* → the matrix with entries (v_i·v_j)²; reason: the matrix of w ↦ L(L*(w)); proved equal in the sanity file
--   - generalization: d-dimensional points, d ≥ 1 implicit → no hypothesis on d; reason: the identity also holds at d = 0 (both sides vanish with Lean's 1/0 = 0); the source's case d ≥ 1 is included
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), §2.3, eq. (2)–(5), p.17 (PDF p.19)

import Mathlib
import Definitions.Def_EllipsoidFitting_matA

set_option autoImplicit false

namespace EllipsoidFitting

open Matrix

/-- **The decomposition `M = A + B`, eq. (2)–(5).** de la Cerda, Potechin, Tulsiani, Xu, *Sharp
Phase Transition for Ellipsoid Fitting*, arXiv:2608.12415 (version of Nov 3, 2026), §2.3,
eq. (2)–(5), p.17: "M = A + B, where A := (1 + 1/d) Im + Mα + Mβ + MD and B := 1/d Jm + 1/d (1m η⊤
+ η 1⊤m)"; "for i ≠ j ∈ [m], Mα[i, j] := ∑_{a≠b∈[d]} vi[a]vi[b]vj[a]vj[b] = 2 · ∑_{a<b∈[d]}
vi[a]vi[b]vj[a]vj[b]".

For every family of points `v`, the Gram matrix `M = (⟨v_i, v_j⟩²)` equals `A + B`, and the two
expressions for `M_α[i, j]` in (3) agree for `i ≠ j`.

**Formalization Note** Deterministic: no probability and no hypothesis on `v` or `d`. At `d = 0`
both sides are `0` (Lean's `1/0 = 0`), so the identity also holds there. -/
theorem eq_2_5 {m d : ℕ} (v : Fin m → Fin d → ℝ) :
    gram v = matA v + matB v ∧
      ∀ i j, i ≠ j →
        Malpha v i j = 2 * ∑ a, ∑ b, if a < b then v i a * v i b * v j a * v j b else 0 := by sorry

end EllipsoidFitting
