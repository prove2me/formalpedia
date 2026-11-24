-- Prove2me | Theorems.Thm_Arxiv1510_02920_mirrored_slab_reflectionless
-- name    : Arxiv1510_02920.mirrored_slab_reflectionless
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T02:12:59.09155+00:00
-- url     : https://prove2.me/theorems/92869b79-fb88-4554-a0f7-36e60b9d6a09
-- title:
--   Fig. 2: the spatially inverted profile and the mirrored slab do not reflect exiting waves
-- statement:
--   Let $c>0$, $a>0$, $\Omega\ne0$, $\gamma>0$, and let $\varepsilon$, $P$, $E$ be as in the paper's example, with $k_0=\omega/c$ and $n_-(\omega)=1+\Omega^2/(\gamma-i\omega)^2$.
--
--   1. *Spatial inversion.* For real $\omega\ne0$, $\varepsilon(-x,\omega)\to1$ as $x\to-\infty$ and $\to n_-(\omega)^2$ as $x\to+\infty$. For $E_0\ne0$, $E(-x)$ solves the Helmholtz equation with permittivity $\varepsilon(-x,\omega)$ at every $x$ and is a left-going wave: $\frac{d}{dx}E(-x)=-ik_0P(-x,\omega)E(-x)$.
--   2. *Mirrored slab.* For every cut position $x_0$ far enough to the left (in the nearly homogeneous region), and every real $\omega\ne0$, the slab permittivity $\varepsilon_s$ tends to $1$ as $x\to\pm\infty$. For $E_0\ne0$ the source field $E_s$ solves the Helmholtz equation with $\varepsilon_s$ at every $x\ne x_0$, and it is purely outgoing on each side of the cut:
--
--   $$E_s'(x)=ik_0P(x,\omega)E_s(x)\ (x>x_0),\qquad E_s'(x)=-ik_0P(2x_0-x,\omega)E_s(x)\ (x<x_0).$$
--
--   There are $T,T'\ne0$ with $E_s(x)e^{-ik_0x}\to T$ as $x\to+\infty$ and $E_s(x)e^{ik_0x}\to T'$ as $x\to-\infty$. So waves exiting through either boundary region are not reflected, at any frequency.
--
--   **Formalization Note** "Not reflected" is expressed as in the paper's method: on each side the field is exactly a one-directional wave of the form (2), with a pure outgoing plane wave in the vacuum. The cut condition "in the (approximately) homogeneous region" is read as "for all sufficiently negative $x_0$". The plane source sits at $x_0$, where the Helmholtz equation is not required to hold.
-- source:
--   T. G. Philbin, All-frequency reflectionlessness, arXiv:1510.02920v1 (2015), claim c016; unnumbered main text, final paragraph and Figure 2, PDF p. 5

import Mathlib
import Definitions.Def_Arxiv1510_02920_Basic

open Filter Topology Asymptotics

namespace Arxiv1510_02920

theorem mirrored_slab_reflectionless (c a Om γ : ℝ) (hc : 0 < c) (ha : 0 < a) (hOm : Om ≠ 0)
    (hγ : 0 < γ) :
    (∀ ω : ℝ, ω ≠ 0 →
      Tendsto (fun x : ℝ => tanhPerm c Om a γ (-x) (ω : ℂ)) atBot (𝓝 1) ∧
      Tendsto (fun x : ℝ => tanhPerm c Om a γ (-x) (ω : ℂ)) atTop
        (𝓝 (mediumIndex Om γ ω ^ 2)) ∧
      ∀ E0 : ℂ, E0 ≠ 0 → ∀ x,
        HelmholtzAt c ω (fun y => tanhPerm c Om a γ (-y) (ω : ℂ))
          (fun y => waveField c E0 (tanhP Om a γ) ω (-y)) x ∧
        deriv (fun y => waveField c E0 (tanhP Om a γ) ω (-y)) x =
          -(Complex.I * ((ω / c : ℝ) : ℂ) * tanhP Om a γ (-x) (ω : ℂ) *
            waveField c E0 (tanhP Om a γ) ω (-x))) ∧
    ∀ᶠ x0 in atBot, ∀ ω : ℝ, ω ≠ 0 →
      Tendsto (fun x : ℝ => slabPerm (tanhPerm c Om a γ) x0 x (ω : ℂ)) atTop (𝓝 1) ∧
      Tendsto (fun x : ℝ => slabPerm (tanhPerm c Om a γ) x0 x (ω : ℂ)) atBot (𝓝 1) ∧
      ∀ E0 : ℂ, E0 ≠ 0 →
        (∀ x, x ≠ x0 → HelmholtzAt c ω (fun y => slabPerm (tanhPerm c Om a γ) x0 y (ω : ℂ))
          (slabField (waveField c E0 (tanhP Om a γ) ω) x0) x) ∧
        (∀ x, x0 < x → deriv (slabField (waveField c E0 (tanhP Om a γ) ω) x0) x =
          Complex.I * ((ω / c : ℝ) : ℂ) * tanhP Om a γ x (ω : ℂ) *
            slabField (waveField c E0 (tanhP Om a γ) ω) x0 x) ∧
        (∀ x, x < x0 → deriv (slabField (waveField c E0 (tanhP Om a γ) ω) x0) x =
          -(Complex.I * ((ω / c : ℝ) : ℂ) * tanhP Om a γ (2 * x0 - x) (ω : ℂ) *
            slabField (waveField c E0 (tanhP Om a γ) ω) x0 x)) ∧
        (∃ T T' : ℂ, T ≠ 0 ∧ T' ≠ 0 ∧
          Tendsto (fun x : ℝ => slabField (waveField c E0 (tanhP Om a γ) ω) x0 x *
            Complex.exp (-(Complex.I * ((ω / c : ℝ) : ℂ) * x))) atTop (𝓝 T) ∧
          Tendsto (fun x : ℝ => slabField (waveField c E0 (tanhP Om a γ) ω) x0 x *
            Complex.exp (Complex.I * ((ω / c : ℝ) : ℂ) * x)) atBot (𝓝 T')) := by sorry

end Arxiv1510_02920
