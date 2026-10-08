-- Prove2me | Theorems.Thm_FeaturePricing_Ellipsoid_volume_update_le
-- name    : FeaturePricing.Ellipsoid.volume_update_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T02:21:57.407242+00:00
-- url     : https://prove2.me/theorems/b4bab41d-2431-49b5-841e-3e26234213b4
-- title:
--   §5.1, p. 14 — Vol E(Ã) ≤ e^{−1/2d} · Vol E(A)
-- statement:
--   Let $d\ge2$, let $A$ be a positive definite $d\times d$ matrix, $x\in\mathbb R^d\setminus\{0\}$, $b=Ax/\sqrt{x'Ax}$ and
--   $$
--   \tilde A=\frac{d^2}{d^2-1}\Big(A-\frac{2}{d+1}bb'\Big)
--   $$
--   the matrix of Eq. (4). Then for all centers $c,c'$
--   $$
--   \operatorname{Vol}E(\tilde A,c')\le e^{-1/2d}\cdot\operatorname{Vol}E(A,c).
--   $$
--
--   This is the "central fact used in the analysis of the ellipsoid method" quoted on p. 14: each exploration step of EllipsoidPricing shrinks the volume of the ellipsoid by the factor $e^{-1/2d}$, which gives the upper bound $\operatorname{Vol}\tilde E_{n+1}/\operatorname{Vol}\tilde E_1\le e^{-n/2d}$ in the proof of Lemma 1.
--
--   **Formalization Note** The volume of an ellipsoid does not depend on its center, so the centers are arbitrary. $\tilde A$ is the published `ellipsoidUpdateMatrix A x`. The platform's proved `LinearOptimization.ellipsoid_update_halfspace_volume` has the weaker factor $e^{-1/(2(d+1))}$, so it does not give this statement.
-- source:
--   Cohen, Lobel, Paes Leme, Feature-Based Dynamic Pricing, Management Science (2020), DOI 10.1287/mnsc.2019.3485 (authors' copy, SSRN 2737045), p. 14, §5.1, display after Eq. (4)

import Mathlib
import Definitions.Def_LinearOptimization_EllipsoidMethod

namespace FeaturePricing.Ellipsoid

open Matrix LinearOptimization MeasureTheory

/-- **§5.1, p. 14.** A central cut of the ellipsoid method shrinks the volume by at least
`e^{−1/(2d)}`: for `d ≥ 2`, `A` positive definite and `x ≠ 0`, with `Ã` the matrix of Eq. (4),
`Vol E(Ã) ≤ e^{−1/(2d)} · Vol E(A)` (the volume does not depend on the centers). -/
theorem volume_update_le {d : ℕ} (hd : 2 ≤ d) (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef)
    (x : Fin d → ℝ) (hx : x ≠ 0) (c c' : Fin d → ℝ) :
    volume (ellipsoid c' (ellipsoidUpdateMatrix A x)) ≤
      ENNReal.ofReal (Real.exp (-1 / (2 * (d : ℝ)))) * volume (ellipsoid c A) := by sorry

end FeaturePricing.Ellipsoid
