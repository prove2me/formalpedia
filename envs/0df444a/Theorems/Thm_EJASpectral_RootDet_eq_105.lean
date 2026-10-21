-- Prove2me | Theorems.Thm_EJASpectral_RootDet_eq_105
-- name    : EJASpectral.RootDet.eq_105
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:03:03.422+00:00
-- url     : https://prove2.me/theorems/771c6998-ff54-4af6-a47a-fd7e6868ad9c
-- title:
--   (105), p. 24 — ∇²Ψ(ũ)[p̃, p̃] = tr(r̂²) = ‖σ‖², σ the eigenvalues of r̂ = P(w^{−1/2})r
-- statement:
--   Let $V$ be a finite-dimensional Euclidean Jordan algebra of rank $d\ge1$, $\Psi(u,w) = -\log\det(w)$, and let $\tilde u = (u,w)\in\operatorname{int}(\mathcal K_{\mathrm{rtdet}})$ and $\tilde p = (p,r)\in\mathbb R\times V$. Let $\hat r := P(w^{-1/2})r$ and let $\sigma\in\mathbb R^d$ be the eigenvalues of $\hat r$. Then
--   $$\nabla^2\Psi(\tilde u)[\tilde p,\tilde p] = \operatorname{tr}(\hat r^2) = \|\sigma\|^2 = \sum_{i\in[\![d]\!]}\sigma_i^2 .$$
--
--   This identifies the local norm of the direction $\tilde p$ in the barrier $\Psi$ with the Euclidean norm of the eigenvalues of the scaled direction $\hat r$; it is the first of the three computations that reduce the compatibility inequality (103) to an inequality about $\sigma$.
--
--   **Formalization Note** The paper states (105) for square roots, $(\nabla^2\Psi(\tilde u)[\tilde p,\tilde p])^{1/2} = \operatorname{tr}(\hat r^2)^{1/2} = \|\sigma\|$. The three quantities are nonnegative, so this is equivalent to the squared form stated here, which avoids the convention that the real square root of a negative number is $0$. $\|\sigma\|$ is the Euclidean norm, written $\sqrt{\sum_i\sigma_i^2}$. $d\ge1$ is added because the paper divides by $d$.
-- source:
--   Coey, Kapelevich & Vielma, Conic optimization with spectral functions on Euclidean Jordan algebras, arXiv:2103.04104v2, p. 24, proof of Proposition 7.1, (105)

import Mathlib
import Definitions.Def_EJASpectral_RootDet_EJA
import Definitions.Def_EJASpectral_RootDet_LHSCB
import Definitions.Def_EJASpectral_RootDet_RootDetCone

namespace EJASpectral.RootDet

/-- (105), p. 24, squared: for `ũ = (u, w) ∈ int K_rtdet` and `p̃ = (p, r)`, with `σ` the
eigenvalues of `r̂ = P(w^{-1/2}) r`, `∇²Ψ(ũ)[p̃, p̃] = tr(r̂²) = ‖σ‖² = Σᵢ σᵢ²`. -/
theorem eq_105 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {d : ℕ} (hd : 0 < d) (J : EJA V d)
    (x : ℝ × V) (hx : x ∈ interior (Krtdet J)) (h : ℝ × V) :
    iteratedFDeriv ℝ 2 (Psi J) x (fun _ => h) =
        J.tr (J.jmul (rhat J x.2 h.2) (rhat J x.2 h.2)) ∧
      J.tr (J.jmul (rhat J x.2 h.2) (rhat J x.2 h.2)) =
        ∑ i, J.eig (rhat J x.2 h.2) i ^ 2 := by sorry

end EJASpectral.RootDet
