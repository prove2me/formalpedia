-- Prove2me | Theorems.Thm_EllipsoidFitting_claim_3_6
-- name    : EllipsoidFitting.claim_3_6
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T10:42:14.313164+00:00
-- url     : https://prove2.me/theorems/17cefa45-af63-43ef-a2c1-568ffc793ddb
-- title:
--   Claim 3.6 (corrected: $1/2<\gamma<1$) — $c_R>\frac{1-\gamma}\gamma$
-- statement:
--   Let $1/2<\gamma<1$ and $C\ne0$ (the paper's constant is $C=C_F=8/(3\pi)$). Then
--   $$
--   c_R:=\sqrt{\frac{1-\gamma}\gamma\cdot\frac1{C^2}\cdot\Bigl(1-\frac{1-\gamma}\gamma\,(1-C^2)\Bigr)}\;>\;\frac{1-\gamma}\gamma .
--   $$
--
--   With this $c_R$ the dual inner matrix has variance $1$ and the target witness of Definition 3.3 has $\langle\Lambda,I-R\rangle<0$, which is why $\gamma>1/2$, i.e. $m>d^2/4$, is the refutation threshold.
--
--   **Formalization Note** The printed hypothesis is only $\gamma>1/2$; see the correction below.
--
--   Differences from the source:
--   - correction: γ > 1/2 → 1/2 < γ < 1; reason: false at γ = 1: ρ = (1−γ)/γ = 0, the radicand is 0 and c_R = 0 = ρ, not > ρ; for γ > 1 the radicand ρ(1 − ρ(1 − C_F²))/C_F² is negative and c_R is undefined; the proof's '0 < ρ < 1 for γ > 1/2' holds exactly for 1/2 < γ < 1
--   - generalization: the constant C_F = 8/(3π) → any real C ≠ 0; reason: the proof uses only C ≠ 0 (c_R² − ρ² = ρ(1 − ρ)/C²); C_F ≠ 0 is the source's case
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), Claim 3.6, p.40 (PDF p.42)

import Mathlib

set_option autoImplicit false

namespace EllipsoidFitting

/-- **Claim 3.6 (corrected: `1/2 < γ < 1`).** de la Cerda, Potechin, Tulsiani, Xu, *Sharp Phase
Transition for Ellipsoid Fitting*, arXiv:2608.12415 (version of Nov 3, 2026), Claim 3.6, p.40:
"For cR = √((1−γ)/γ · 1/C²_F · (1 − (1−γ)/γ (1 − C²_F))), we have cR > (1−γ)/γ provided γ > 1/2
which is exactly our desired threshold for refutation."

For `1/2 < γ < 1` and every nonzero constant `C` (the paper's is `C_F = 8/(3π)`),
`√((1−γ)/γ · 1/C² · (1 − (1−γ)/γ · (1 − C²))) > (1−γ)/γ`.

**Formalization Note** Correction: as printed (`γ > 1/2`) the claim is false at `γ = 1`, where
`(1−γ)/γ = 0`, the radicand is `0` and `c_R = 0 = (1−γ)/γ`; for `γ > 1` the radicand is negative
(for `C = C_F`) and `c_R` is undefined. The proof's "0 < ρ < 1 for γ > 1/2" holds exactly for
`1/2 < γ < 1`. Stated for every `C ≠ 0`, which contains the case `C = C_F`. -/
theorem claim_3_6 (γ C : ℝ) (hC : C ≠ 0) (hγ1 : 1 / 2 < γ) (hγ2 : γ < 1) :
    (1 - γ) / γ <
      Real.sqrt ((1 - γ) / γ * (1 / C ^ 2) * (1 - (1 - γ) / γ * (1 - C ^ 2))) := by sorry

end EllipsoidFitting
