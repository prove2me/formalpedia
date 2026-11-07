-- Prove2me | Theorems.Thm_EllipsoidFitting_proposition_2_3
-- name    : EllipsoidFitting.proposition_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:13.559946+00:00
-- url     : https://prove2.me/theorems/391f7f35-9d50-418c-836f-34989d77b7ae
-- title:
--   Proposition 2.3 — primal invariant $L(\frac1{C_F}F(Q_i))-\mathbf 1_m=\frac1{C_F}L(H_i)$
-- statement:
--   Let $v_1,\dots,v_m\in\mathbb R^d$ have invertible Gram matrix $M$ and $\gamma=2m/d^2\ne1$, and let $c\ne0$ (the paper's normalizer is $c=C_F=8/(3\pi)$). Let $(Q_i,H_i)$ be the primal iteration with normalizer $c$. Then for every $i\ge0$,
--   $$
--   L\Bigl(\frac1c\,F(Q_i)\Bigr)-\mathbf 1_m=\frac1c\,L(H_i).
--   $$
--
--   At every step the entire constraint violation of the candidate $\frac1{C_F}F(Q_i)$ comes from the newest higher-order term $H_i$, so the construction converges when the $H_i$ shrink.
--
--   **Formalization Note** Deterministic. $F(Q_i)$ is the spectral map (`cfc`); the iterates are symmetric (proved in the sanity file).
--
--   Differences from the source:
--   - generalization: the normalizer C_F → any c ≠ 0 (the iteration and G built with c); reason: the identity is algebraic in c; c = C_F = 8/(3π) ≠ 0 is the source's case
--   - generalization: for any i ≥ 1 → for every i ≥ 0; reason: the identity also holds at i = 0; i ≥ 1 is included
--   - encoding: M⁻¹ and 1/(1 − γ) in the update → hypotheses det M a unit and γ ≠ 1; reason: only exclude cases where the update is undefined
--   - reading: H_i := ∑_{j≥2} b_j (P_j(X_i) − P_j(X_{i−1})), H_0 := ∑_{j≥2} b_j P_j(X_0) → H_i = G(X_i) − G(X_{i−1}), H_0 = G(X_0) with G(X) = F(X) − C_F·I − X; reason: the matrix series does not converge off [−2,2]; G is the function the series represents in L²(µsc)
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), Proposition 2.3, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_EllipsoidFitting_primalIter

set_option autoImplicit false

namespace EllipsoidFitting

open Matrix

/-- **Proposition 2.3 (invariant for the iterative process).** de la Cerda, Potechin, Tulsiani,
Xu, *Sharp Phase Transition for Ellipsoid Fitting*, arXiv:2608.12415 (version of Nov 3, 2026),
Proposition 2.3, p.10: "For any i ≥ 1, we have L(1/CF F(Qi)) − 1m = 1/CF · L(Hi)."

For every family of points with `M` invertible and `γ = 2m/d² ≠ 1`, every nonzero normalizer
`c` (the paper's is `c = C_F = 8/(3π)`) and every `i ≥ 0`, the primal iterates satisfy
`L(F(Q_i)/c) − 1_m = L(H_i)/c`.

**Formalization Note** Deterministic. `M` invertible and `γ ≠ 1` are needed for the update
`correct` (it uses `M⁻¹` and `1/(1−γ)`). Stated for every `i ≥ 0` (the identity also holds at
`i = 0`) and for every `c ≠ 0`; the paper's statement is the case `c = C_F`, `i ≥ 1`. -/
theorem proposition_2_3 {m d : ℕ} (v : Fin m → Fin d → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hM : IsUnit (gram v).det) (hγ : gammaRatio d m ≠ 1) (i : ℕ) :
    constraintMap v ((1 / c) • cfc Fpos (primalQ v c i)) - (fun _ => (1 : ℝ)) =
      (1 / c) • constraintMap v (primalH v c i) := by sorry

end EllipsoidFitting
