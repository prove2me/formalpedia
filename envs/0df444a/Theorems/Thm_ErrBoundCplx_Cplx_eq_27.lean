-- Prove2me | Theorems.Thm_ErrBoundCplx_Cplx_eq_27
-- name    : ErrBoundCplx.Cplx.eq_27
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:10.774784+00:00
-- url     : https://prove2.me/theorems/2eb6ed6a-46c0-417b-83d2-2f418ccd4494
-- title:
--   (27), proof of Theorem 16 — if f(x_k) > 0 then s_k = (β_{k−1} − β_k)/ψ′(β_k) ≥ ζ with β_j = φ(f(x_j))
-- statement:
--   Assume the setting of Theorem 16: $H$ is a real Hilbert space, $f : H \to (-\infty, +\infty]$ is proper, lower semicontinuous and convex with $\min f = 0$ attained, $f$ has the KL property on $[0 < f < \bar r]$ with desingularizing function $\varphi \in \mathcal K(0, \bar r)$, $(x_k)$ is a subgradient descent sequence with constants $a, b > 0$ and $f(x_0) = r_0 \in (0, \bar r)$, $\alpha_0 = \varphi(r_0)$, $\psi = (\varphi|_{[0, r_0]})^{-1}$ satisfies (A) with constant $\ell$, and $\zeta$ is given by (21).
--
--   For $j \ge 0$ let $r_j = f(x_j)$ and $\beta_j = \psi^{-1}(r_j) = \varphi(r_j)$. If $k \ge 1$ and $r_k > 0$, then
--   $$s_k := \frac{\beta_{k-1} - \beta_k}{\psi'(\beta_k)} \ \ge\ \frac{\sqrt{1 + 2\ell a b^{-2}} - 1}{\ell} = \zeta.$$
--
--   This lower bound on the implicit step sizes $s_k$, for which $\beta_k = (I + s_k\psi')^{-1}(\beta_{k-1})$, is what allows the comparison of $(\beta_k)$ with the worst-case proximal sequence $(\alpha_k)$, whose step is $\zeta$.
--
--   **Formalization Note** $\beta_j$ is written as $\varphi(f(x_j))$ (with $f(x_j)$ a real number in $[0, r_0]$, entering through `toReal`), since $\psi^{-1} = \varphi$ on $[0, r_0]$; $\psi'$ is the derivative of $\psi$ within $[0, \alpha_0]$.
-- source:
--   arXiv:1510.08234v3, proof of Theorem 16, (26)–(27), p. 18

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonconvexSplitting_ADMMKL_KLProperty
import Definitions.Def_ErrBoundCplx_Cplx_DescentSeq
import Definitions.Def_ErrBoundCplx_Cplx_WorstCase
open MoreauProx.Characterization NonconvexSplitting.ADMMKL
open Filter Topology

namespace ErrBoundCplx.Cplx

/-- arXiv:1510.08234v3, proof of Theorem 16, (27), p. 18. In the setting of Theorem 16, for every
`k ≥ 1` with `r_k = f(x_k) > 0`, put `β_j = ψ⁻¹(r_j) = φ(r_j)`; then
`s_k = (β_{k−1} − β_k)/ψ'(β_k) ≥ ζ`, with `ζ` of (21). -/
theorem eq_27 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → EReal) (hf : GammaZero f) (hmin : IsMinZero f)
    (φ ψ : ℝ → ℝ) (rbar r0 : ℝ) (ℓ : NNReal) (hS : ProfileSetting φ ψ rbar r0 ℓ)
    (hKL : KLOnBand f rbar φ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (x : ℕ → H) (hx : IsSubgradDescentSeq f a b x)
    (hx0 : f (x 0) = (r0 : EReal))
    (k : ℕ) (hk : 1 ≤ k) (hrk : 0 < f (x k)) :
    zeta ℓ a b ≤ (φ (f (x (k - 1))).toReal - φ (f (x k)).toReal)
      / psiPrime ψ (φ r0) (φ (f (x k)).toReal) := by sorry

end ErrBoundCplx.Cplx
