-- Prove2me | Theorems.Thm_EllipsoidFitting_lemma_2_18
-- name    : EllipsoidFitting.lemma_2_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:10.755911+00:00
-- url     : https://prove2.me/theorems/3991582c-e4bb-4797-ae85-47b7d409cb90
-- title:
--   Lemma 2.18 — explicit inverse of $M$
-- statement:
--   Let $r=\mathbf 1_m^\top A^{-1}\mathbf 1_m/d$, $s=1+\eta^\top A^{-1}\mathbf 1_m/d$, $u=-1+\eta^\top A^{-1}\eta/d$. If $A$ is invertible and $s^2-ru\ne0$, then $M$ is invertible and
--   $$
--   M^{-1}=A^{-1}+\frac1{s^2-ru}\,A^{-1}\Bigl(u\,\frac{\mathbf 1_m\mathbf 1_m^\top}{d}-s\,\frac{\eta\mathbf 1_m^\top+\mathbf 1_m\eta^\top}{d}+r\,\frac{\eta\eta^\top}{d}\Bigr)A^{-1}.\qquad(10)
--   $$
--
--   Combined with the polynomial expansion of $A^{-1}$ this gives the explicit $M^{-1}$ used by every correction step.
--
--   **Formalization Note** Deterministic; holds for every family of points satisfying the two nondegeneracy conditions (which hold with high probability by Lemma 4.14 / Corollary 4.15).
--
--   Differences from the source:
--   - encoding: A⁻¹ and 1/(s² − ru) used without stated invertibility → hypotheses det A a unit and s² − ru ≠ 0; reason: Lean's inverses are total (junk 0); the conditions only exclude cases where (10) is undefined
--   - encoding: M⁻¹ = (10), M invertible presupposed → IsUnit (det M) ∧ M⁻¹ = (10); reason: Lean's M⁻¹ is total, so the invertibility the printed equation presupposes is stated
--   - encoding: d ≥ 1 implicit → no hypothesis on d; reason: for d = 0 and m ≥ 1, A = 0 is singular and is excluded by the hypothesis on A; m = 0 is the empty case
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), Lemma 2.18, eq. (10), p.24 (PDF p.26)

import Mathlib
import Definitions.Def_EllipsoidFitting_scalarR

set_option autoImplicit false

namespace EllipsoidFitting

open Matrix

/-- **Lemma 2.18 (explicit inverse of `M`).** de la Cerda, Potechin, Tulsiani, Xu, *Sharp Phase
Transition for Ellipsoid Fitting*, arXiv:2608.12415 (version of Nov 3, 2026), Lemma 2.18, eq. (10),
p.24: "Let r := 1T_m A−1 1m / d , s := 1 + ηT A−1 1m / d , u := −1 + ηT A−1 η / d . Then M−1 = A−1 +
1/(s² − ru) A−1 ( u 1m1T_m / d − s (η1T_m + 1mηT)/d + r ηηT/d ) A−1."

If `A` is invertible and `s² − ru ≠ 0`, then `M` is invertible and its inverse is given by (10).

**Formalization Note** The formula divides by `s² − ru` and uses `A⁻¹`; Lean's `Matrix.inv` and
`1/0` are junk values `0`, so both nondegeneracy conditions are hypotheses (they hold with high
probability, Corollary 4.15). The conclusion also asserts that `M` is invertible, which the
printed equation presupposes. -/
theorem lemma_2_18 {m d : ℕ} (v : Fin m → Fin d → ℝ) (hA : IsUnit (matA v).det)
    (hsru : scalarS v ^ 2 - scalarR v * scalarU v ≠ 0) :
    IsUnit (gram v).det ∧
      (gram v)⁻¹ = (matA v)⁻¹ + (1 / (scalarS v ^ 2 - scalarR v * scalarU v)) •
        ((matA v)⁻¹ *
          ((scalarU v / (d : ℝ)) • vecMulVec (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) -
            (scalarS v / (d : ℝ)) •
              (vecMulVec (eta v) (fun _ => (1 : ℝ)) + vecMulVec (fun _ => (1 : ℝ)) (eta v)) +
            (scalarR v / (d : ℝ)) • vecMulVec (eta v) (eta v)) *
          (matA v)⁻¹) := by sorry

end EllipsoidFitting
