-- Prove2me | Theorems.Thm_DistCov_Hilbert_gaussEmb_isometry
-- name    : DistCov.Hilbert.gaussEmb_isometry
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T06:28:14.915416+00:00
-- url     : https://prove2.me/theorems/c90597aa-5b18-4432-9f69-0d6594013951
-- title:
--   p. 18 — Gaussian Crofton embedding: ‖ϕ(u) − ϕ(u′)‖₂² = ‖ϕ(u) − ϕ(u′)‖₁ = ‖u − u′‖₂
-- statement:
--   Let $\rho$ be the IID standard normal law on $\mathbb R^\infty$, $\lambda$ Lebesgue measure on $\mathbb R$, $c=\mathbf E|Z_1|$, and for $u\in\ell^2(\mathbb Z^+)$ let
--   $$\phi(u)(w,s)=\mathbf 1_{[w(u)/c,\infty)}(s)-\mathbf 1_{[0,\infty)}(s),\qquad w(u)=\limsup_N\sum_{n=1}^N u_nw_n .$$
--   Then for all $u,u'\in\ell^2(\mathbb Z^+)$ the functions $(\phi(u)-\phi(u'))^2$ and $|\phi(u)-\phi(u')|$ are integrable with respect to $\rho\times\lambda$, and
--   $$\int (\phi(u)-\phi(u'))^2\,d(\rho\times\lambda) = \int |\phi(u)-\phi(u')|\,d(\rho\times\lambda) = \|u-u'\|_2 .$$
--
--   Thus $\phi$ embeds $(\ell^2(\mathbb Z^+),\|\cdot\|_2^{1/2})$ isometrically into $L^2(\rho\times\lambda)$: it is the embedding through which the paper computes $D(\mu_1-\mu_2)$ on $\ell^2$.
--
--   **Formalization Note.** $\phi(u)$ is a plain real function on $\mathbb R^\infty\times\mathbb R$; the squared $L^2$ norm and the $L^1$ norm of the paper are the two integrals. The integrability clauses are added so the integrals are not Lean's junk value $0$. Indices start at $0$.
-- source:
--   Lyons, Distance covariance in metric spaces, arXiv:1106.5758 (version of 19 Dec. 2020), p. 18, proof of Theorem 3.16, display defining ϕ(u) and the sentence after it

import Mathlib
import Definitions.Def_DistCov_Hilbert_Setting

namespace DistCov.Hilbert

open MeasureTheory ProbabilityTheory

theorem gaussEmb_isometry (u u' : DistCov.Indep.L2N) :
    Integrable (fun p => (gaussEmb u p - gaussEmb u' p) ^ 2) (rho.prod volume) ∧
    ∫ p, (gaussEmb u p - gaussEmb u' p) ^ 2 ∂(rho.prod volume) = ‖u - u'‖ ∧
    Integrable (fun p => |gaussEmb u p - gaussEmb u' p|) (rho.prod volume) ∧
    ∫ p, |gaussEmb u p - gaussEmb u' p| ∂(rho.prod volume) = ‖u - u'‖ := by sorry

end DistCov.Hilbert
