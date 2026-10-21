-- Prove2me | Theorems.Thm_EJASpectral_RootDet_eq_107
-- name    : EJASpectral.RootDet.eq_107
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:10.769838+00:00
-- url     : https://prove2.me/theorems/4532be08-30f5-407f-8a48-e2776540d19b
-- title:
--   (107), p. 24 — ∇²φ(w)[r, r] = −d⁻¹ φ Σᵢ δᵢ² ≤ 0
-- statement:
--   Let $V$ be a finite-dimensional Euclidean Jordan algebra of rank $d\ge1$ with cone of squares $\mathcal Q$, and let $\varphi(w) = \det(w)^{1/d}$. Let $w\in\operatorname{int}(\mathcal Q)$ (i.e. $w\succ0$) and $r\in V$. Let $\hat r := P(w^{-1/2})r$, let $\sigma\in\mathbb R^d$ be its eigenvalues, $m_1 := d^{-1}\sum_i\sigma_i$ and $\delta_i := \sigma_i - m_1$. Then
--   $$\nabla^2\varphi(w)[r,r] = -d^{-1}\varphi(w)\sum_{i\in[\![d]\!]}\delta_i^2 \le 0 . \tag{107d}$$
--
--   The second directional derivative of the root-determinant is minus a multiple of the variance of the eigenvalues of $\hat r$. It shows concavity of $\varphi$ on $\operatorname{int}(\mathcal Q)$ and enters (109) as the factor $\nabla^2\zeta = \nabla^2\varphi$.
--
--   **Formalization Note** The statement records the end of the chain (107a)–(107d); the intermediate expressions are steps of the computation. $m_1 = d^{-1}\operatorname{tr}(\hat r)$ is written as $d^{-1}\sum_i\sigma_i$. $d\ge1$ is added because the paper divides by $d$.
-- source:
--   Coey, Kapelevich & Vielma, Conic optimization with spectral functions on Euclidean Jordan algebras, arXiv:2103.04104v2, p. 24, proof of Proposition 7.1, (107a)–(107d)

import Mathlib
import Definitions.Def_EJASpectral_RootDet_EJA
import Definitions.Def_EJASpectral_RootDet_LHSCB
import Definitions.Def_EJASpectral_RootDet_RootDetCone

namespace EJASpectral.RootDet

/-- (107), p. 24: for `w ≻ 0` and `r ∈ V`, with `σ` the eigenvalues of `r̂ = P(w^{-1/2}) r`,
`m₁ = d⁻¹ Σᵢ σᵢ` and `δᵢ = σᵢ − m₁`, `∇²φ(w)[r, r] = −d⁻¹ φ(w) Σᵢ δᵢ² ≤ 0`. -/
theorem eq_107 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {d : ℕ} (hd : 0 < d) (J : EJA V d)
    (w : V) (hw : w ∈ interior J.Q) (r : V) :
    iteratedFDeriv ℝ 2 (rtdet J) w (fun _ => r) =
        -((d : ℝ))⁻¹ * rtdet J w *
          ∑ i, (J.eig (rhat J w r) i - ((d : ℝ))⁻¹ * ∑ j, J.eig (rhat J w r) j) ^ 2 ∧
      iteratedFDeriv ℝ 2 (rtdet J) w (fun _ => r) ≤ 0 := by sorry

end EJASpectral.RootDet
