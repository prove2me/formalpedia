-- Prove2me | Theorems.Thm_EllipsoidFitting_proposition_3_5
-- name    : EllipsoidFitting.proposition_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:44:53.778541+00:00
-- url     : https://prove2.me/theorems/d397fbc8-162b-4cde-87c2-d286608b70e0
-- title:
--   Proposition 3.5 — dual invariant $\Pi_S^\perp(\frac1{C_F}F(W_i)-\Pi_S^\perp I_d)=\frac1{C_F}\Pi_S^\perp H_i$
-- statement:
--   Let $v_1,\dots,v_m\in\mathbb R^d$ have invertible Gram matrix $M$, let $c\ne0$ (the paper's is $C_F$) and $c_R\in\mathbb R$, and let $(W_i,H_i)$ be the dual iteration. Then for every $i\ge0$,
--   $$
--   \Pi_S^\perp\Bigl(\frac1c\,F(W_i)-\Pi_S^\perp I_d\Bigr)=\frac1c\,\Pi_S^\perp H_i
--   \qquad\text{and}\qquad
--   \frac1c\,F(W_i)-I_d-\frac1c\,H_i\in S .
--   $$
--
--   At every step the whole violation of the image constraint $\frac1{C_F}F(W)\in S$ comes from the newest higher-order term.
--
--   **Formalization Note** Deterministic; both equivalent forms on the page are asserted.
--
--   Differences from the source:
--   - generalization: the normalizer C_F and c_R > 0 chosen later → any c ≠ 0 and any real c_R; reason: the identity is algebraic in c and c_R; c = C_F and the paper's c_R are included
--   - encoding: Π_S = L*M⁻¹L → hypothesis det M a unit; reason: only excludes the case where Π_S is undefined
--   - reading: H_i := ∑_{j≥2} b_j (P_j(X_i) − P_j(X_{i−1})), H_0 := ∑_{j≥2} b_j P_j(X_0) → H_i = G(X_i) − G(X_{i−1}), H_0 = G(X_0) with G(X) = F(X) − C_F·I − X; reason: the matrix series does not converge off [−2,2]; G is the function the series represents in L²(µsc)
--   - reading: H_0 = (1/C_F)∑_{j≥2} b_j P_j(C_F c_R R) (underbrace, p.37) → H_0 = G(W_0), unscaled; reason: the summary (p.38) and the proof (p.39: F(W_0) = C_F I_d + W_0 + H_0) use the unscaled H_0
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), Proposition 3.5, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_EllipsoidFitting_dualIter

set_option autoImplicit false

namespace EllipsoidFitting

open Matrix

/-- **Proposition 3.5 (invariant for the dual iterative process).** de la Cerda, Potechin,
Tulsiani, Xu, *Sharp Phase Transition for Ellipsoid Fitting*, arXiv:2608.12415 (version of Nov 3,
2026), Proposition 3.5, p.38: "For every i ≥ 0, Π⊥_S (1/CF F(Wi) − Π⊥_S Id) = 1/CF Π⊥_S Hi.
Equivalently, 1/CF F(Wi) − Id − 1/CF Hi ∈ S."

For every family of points with `M` invertible, every nonzero normalizer `c` (the paper's is
`C_F`), every real `c_R` and every `i ≥ 0`, the dual iterates satisfy both
`Π⊥_S(F(W_i)/c − Π⊥_S I) = Π⊥_S H_i / c` and `F(W_i)/c − I − H_i/c ∈ S`.

**Formalization Note** Deterministic; `M` invertible because `Π_S` uses `M⁻¹`. Stated for every
`c ≠ 0` and every real `c_R` (the paper fixes `c = C_F` and a positive `c_R` chosen later).
Both formulations of the page are asserted. -/
theorem proposition_3_5 {m d : ℕ} (v : Fin m → Fin d → ℝ) (c : ℝ) (hc : c ≠ 0) (cR : ℝ)
    (hM : IsUnit (gram v).det) (i : ℕ) :
    projSperp v ((1 / c) • cfc Fpos (dualW v c cR i) - projSperp v 1) =
        (1 / c) • projSperp v (dualH v c cR i) ∧
      (1 / c) • cfc Fpos (dualW v c cR i) - 1 - (1 / c) • dualH v c cR i ∈ imageS v := by sorry

end EllipsoidFitting
