-- Prove2me | Theorems.Thm_EJASpectral_RootDet_eq_108
-- name    : EJASpectral.RootDet.eq_108
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:13.207151+00:00
-- url     : https://prove2.me/theorems/1f0a488a-7146-45ed-8835-3424bfdaf2b4
-- title:
--   (108), pp. 24–25 — ∇³φ(w)[r, r, r] = d⁻¹ φ Σᵢ δᵢ² (m₁ + 2σᵢ)
-- statement:
--   Let $V$ be a finite-dimensional Euclidean Jordan algebra of rank $d\ge1$ with cone of squares $\mathcal Q$, and let $\varphi(w) = \det(w)^{1/d}$. Let $w\in\operatorname{int}(\mathcal Q)$ and $r\in V$. Let $\hat r := P(w^{-1/2})r$, let $\sigma\in\mathbb R^d$ be its eigenvalues, $m_1 := d^{-1}\sum_i\sigma_i$ and $\delta_i := \sigma_i - m_1$. Then
--   $$\nabla^3\varphi(w)[r,r,r] = d^{-1}\varphi(w)\sum_{i\in[\![d]\!]}\delta_i^2\,(m_1 + 2\sigma_i). \tag{108f}$$
--
--   Together with (105) and (107), this expresses the compatibility inequality (103) entirely in terms of the eigenvalues $\sigma$.
--
--   **Formalization Note** The statement records the end of the chain (108a)–(108f). $d\ge1$ is added because the paper divides by $d$.
-- source:
--   Coey, Kapelevich & Vielma, Conic optimization with spectral functions on Euclidean Jordan algebras, arXiv:2103.04104v2, pp. 24–25, proof of Proposition 7.1, (108a)–(108f)

import Mathlib
import Definitions.Def_EJASpectral_RootDet_EJA
import Definitions.Def_EJASpectral_RootDet_LHSCB
import Definitions.Def_EJASpectral_RootDet_RootDetCone

namespace EJASpectral.RootDet

/-- (108), pp. 24–25: for `w ≻ 0` and `r ∈ V`, with `σ` the eigenvalues of `r̂ = P(w^{-1/2}) r`,
`m₁ = d⁻¹ Σᵢ σᵢ` and `δᵢ = σᵢ − m₁`, `∇³φ(w)[r, r, r] = d⁻¹ φ(w) Σᵢ δᵢ² (m₁ + 2σᵢ)`. -/
theorem eq_108 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {d : ℕ} (hd : 0 < d) (J : EJA V d)
    (w : V) (hw : w ∈ interior J.Q) (r : V) :
    iteratedFDeriv ℝ 3 (rtdet J) w (fun _ => r) =
      ((d : ℝ))⁻¹ * rtdet J w *
        ∑ i, (J.eig (rhat J w r) i - ((d : ℝ))⁻¹ * ∑ j, J.eig (rhat J w r) j) ^ 2 *
          (((d : ℝ))⁻¹ * ∑ j, J.eig (rhat J w r) j + 2 * J.eig (rhat J w r) i) := by sorry

end EJASpectral.RootDet
