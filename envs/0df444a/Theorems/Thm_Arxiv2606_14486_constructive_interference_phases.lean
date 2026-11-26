-- Prove2me | Theorems.Thm_Arxiv2606_14486_constructive_interference_phases
-- name    : Arxiv2606_14486.constructive_interference_phases
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T19:08:53.21008+00:00
-- url     : https://prove2.me/theorems/8a456569-b796-4002-bdd3-254799b4e140
-- title:
--   Eq. (4): in-phase condition for beamforming from $\theta_1$ to $\theta_2$
-- statement:
--   Consider an array of $n$ elements spaced $d>0$ along $x$, with wavenumber $k>0$. A wave arrives at angle $\theta_1>0$ and is to be reflected toward $\theta_2>0$. Element $i$ reflects with coefficient $R_ie^{j\psi_i}$, $R_i>0$. The reflected wavefront has entries
--
--   $$y_i=e^{jk(i-1)d\sin\theta_2}\,R_ie^{j\psi_i}\,e^{-jk(i-1)d\sin\theta_1}.$$
--
--   The $y_i$ are all in phase if and only if, for some constant $c$ and for every $i$,
--
--   $$\psi_i\equiv c+(i-1)\Delta\psi\pmod{2\pi},\qquad \Delta\psi=kd(\sin\theta_1-\sin\theta_2).$$
--
--   This is the phase profile that steers the beam from $\theta_1$ to $\theta_2$.
--
--   **Formalization Note** The paper gives the profile as the condition for constructive interference, "up to a constant". The statement proves both directions and makes explicit the additive multiples of $2\pi$ per element, which the paper does not mention. The magnitudes $R_i$ are assumed positive. Without this, the phase of an element with $R_i=0$ is unconstrained.
-- source:
--   Khankhoje and Kundu, Implications of the Reciprocity Theorem for Reconfigurable Intelligent Surfaces, arXiv:2606.14486v1 (2026), claim c013; Sec. II-A (RIS with continuous phase shifts), eqs. (1)-(4), PDF p. 2

import Mathlib
import Definitions.Def_Arxiv2606_14486_Basic

open MeasureTheory

namespace Arxiv2606_14486

theorem constructive_interference_phases {n : ℕ} (k d θ₁ θ₂ : ℝ) (hk : 0 < k) (hd : 0 < d)
    (hθ₁ : 0 < θ₁) (hθ₂ : 0 < θ₂) (R ψ : Fin n → ℝ) (hR : ∀ i, 0 < R i) :
    InPhase (wavefront n k d θ₂ (-θ₁) (reflCoeffs R ψ)) ↔
      ∃ c : ℝ, ∀ i : Fin n, ∃ m : ℤ,
        ψ i = linearPhases n c (phaseStep k d θ₁ θ₂) i + 2 * m * Real.pi := by sorry

end Arxiv2606_14486
