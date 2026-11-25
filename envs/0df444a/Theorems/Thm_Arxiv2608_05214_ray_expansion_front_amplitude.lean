-- Prove2me | Theorems.Thm_Arxiv2608_05214_ray_expansion_front_amplitude
-- name    : Arxiv2608_05214.ray_expansion_front_amplitude
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:16:05.805306+00:00
-- url     : https://prove2.me/theorems/c943c315-cbdc-47da-9e4a-6d9e55c5da64
-- title:
--   Eq. (20): the amplitude of the tail at the wave front is $a_1(\tau)=-\frac12\int_0^\tau q$
-- statement:
--   Let $q:\mathbb R\to\mathbb R$ be smooth with $q=0$ on $(-\infty,0)$. Let $\psi=\delta(t-\tau)+g(\tau,t)H(t-\tau)$ be the causal impulse response of the 1D Schrödinger equation $\partial_t^2\psi-\partial_\tau^2\psi+q\psi=0$ to a unit pulse incident from the left, with reflection response $R$. That is, $g$ is $C^2$ on $\{t\ge\tau\}$, $\psi$ solves the equation in the sense of distributions on $\mathbb R^2$, $g(\tau,t)=R(t+\tau)$ for $\tau<0\le t-\tau$, and $R(t)=0$ for $t<0$. Then the amplitude $a_1(\tau)=g(\tau,\tau)$ of the tail at the wave front satisfies
--
--   $$\frac{da_1}{d\tau}=-\frac{q(\tau)}{2},\qquad a_1(\tau)=-\frac12\int_0^\tau q(\tau')\,d\tau'\quad\text{for all }\tau.$$
--
--   The pulse $\delta(t-\tau)$ travels undistorted, and is followed by a causal tail whose value on the front is $a_1$.
--
--   **Formalization Note** The paper obtains (20) by substituting the formal series (19) and matching the coefficient of each wavelet $f_m$. Here the leading terms of (21), $\delta(t-\tau)+a_1(\tau)H(t-\tau)+\cdots$, are encoded as a distributional solution of the form $\delta(t-\tau)+g\,H(t-\tau)$, and $a_1(\tau)$ is the value of the tail on the front $t=\tau$. The condition $a_1(0)=0$, which the paper uses without saying so, follows from the incident field being a bare pulse. The eikonal equation (a) and the normalisation $a_0=1$ in (b) are built into this form. The higher coefficients $a_n$, $n\ge2$, and the convergence of the series (21) are not stated.
-- source:
--   H. A. Oyekan, Marchenko Theory, Algorithms, and Applications: A Review, arXiv:2608.05214v1 (2026), claim c003; Section III-C (Step 2), eqs. (19)-(21) and the transport hierarchy (a)-(c), PDF pp. 5-6

import Mathlib
import Definitions.Def_Arxiv2608_05214_Basic

open MeasureTheory Filter Topology
open scoped ContDiff

namespace Arxiv2608_05214

theorem ray_expansion_front_amplitude (q : ℝ → ℝ) (hq : ContDiff ℝ ∞ q)
    (hsupp : Function.support q ⊆ Set.Ici 0)
    (g : ℝ × ℝ → ℝ) (R : ℝ → ℝ) (hg : IsImpulseResponseTail q g R) :
    ∀ τ : ℝ, g (τ, τ) = -(1 / 2) * (∫ s in (0 : ℝ)..τ, q s) ∧
      HasDerivAt (fun σ => g (σ, σ)) (-(q τ / 2)) τ := by sorry

end Arxiv2608_05214
