-- Prove2me | Theorems.Thm_EJASpectral_RootDet_rtdet_concave_homogeneous
-- name    : EJASpectral.RootDet.rtdet_concave_homogeneous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:04.305983+00:00
-- url     : https://prove2.me/theorems/432d7d46-0d8c-4065-8630-383250fecea2
-- title:
--   (96), p. 23 — the root-determinant φ = det^{1/d} is nonnegative, concave and homogeneous on Q
-- statement:
--   Let $V$ be a finite-dimensional Euclidean Jordan algebra of rank $d\ge1$ with cone of squares $\mathcal Q$, and let $\varphi(w) = \det(w)^{1/d}$ be the root-determinant (96). Then
--
--   1. $\varphi(w)\ge 0$ for every $w\in\mathcal Q$ (so $\varphi:\mathcal Q\to\mathbb R_\ge$);
--   2. $\varphi$ is concave on $\mathcal Q$;
--   3. $\varphi$ is homogeneous: $$\varphi(\theta w) = \theta\,\varphi(w)\qquad w\in\mathcal Q,\ \theta\ge0.$$
--
--   Concavity of $\varphi$ is what makes $\mathcal K_{\mathrm{rtdet}}$ convex, and homogeneity is what makes it a cone and $\Gamma$ logarithmically homogeneous.
--
--   **Formalization Note** The paper also calls $\varphi$ a "nonseparable spectral function"; that is descriptive and is not formalized. $d\ge1$ is added because the paper divides by $d$.
-- source:
--   Coey, Kapelevich & Vielma, Conic optimization with spectral functions on Euclidean Jordan algebras, arXiv:2103.04104v2, p. 23, §7.1, (96) and the sentence after it

import Mathlib
import Definitions.Def_EJASpectral_RootDet_EJA
import Definitions.Def_EJASpectral_RootDet_LHSCB
import Definitions.Def_EJASpectral_RootDet_RootDetCone

namespace EJASpectral.RootDet

/-- (96), p. 23: `φ = det^{1/d}` maps `Q` to `ℝ≥`, is concave on `Q` and is homogeneous
(`φ(θw) = θ φ(w)` for `θ ≥ 0`). -/
theorem rtdet_concave_homogeneous {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {d : ℕ} (hd : 0 < d) (J : EJA V d) :
    (∀ w ∈ J.Q, 0 ≤ rtdet J w) ∧ ConcaveOn ℝ J.Q (rtdet J) ∧
      ∀ w ∈ J.Q, ∀ θ : ℝ, 0 ≤ θ → rtdet J (θ • w) = θ * rtdet J w := by sorry

end EJASpectral.RootDet
