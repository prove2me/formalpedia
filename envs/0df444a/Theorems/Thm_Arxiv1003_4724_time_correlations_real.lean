-- Prove2me | Theorems.Thm_Arxiv1003_4724_time_correlations_real
-- name    : Arxiv1003_4724.time_correlations_real
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T23:56:56.644882+00:00
-- url     : https://prove2.me/theorems/74d0c3e7-f678-405e-8b81-91846c2ed072
-- title:
--   Eq. (31): the time correlation functions $\sigma(t)$ and $\varphi(t)$ are real
-- statement:
--   In a long-wavelength model (a stationary state, a $*$-automorphism evolution, self-adjoint $P^\beta$ and $I^\beta$ with $dP^\beta/dt=I^\beta$), let $\hbar>0$ and $V>0$. Then the time correlation functions of eq. (31),
--
--   $$\sigma(t)=\frac{i}{3\hbar V}\langle[I^\beta(t),P^\beta(0)]\rangle,\qquad \varphi(t)=-\frac{i}{3\hbar V}\langle[I^\beta(t),I^\beta(0)]\rangle$$
--
--   (summed over $\beta$), are real for every real $t$.
--
--   These are the real kernels whose transforms $\sigma^{(0)}(\omega)$ and $\varphi^{(0)}(\omega)$ (eq. 30) make up $\varepsilon^{(0)}(\omega)$ (eq. 29).
-- source:
--   Bobrov, Trigger, van Heijst and Schram, Kramers-Kronig relations for the dielectric function and the static conductivity of Coulomb systems, arXiv:1003.4724v1 (2010), claim c007; Sec. III, eq. (31) and the sentence after it, PDF p. 6

import Mathlib
import Definitions.Def_Arxiv1003_4724_Basic

open MeasureTheory Filter Topology

namespace Arxiv1003_4724

theorem time_correlations_real {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A]
    (ω : A →ₗ[ℂ] ℂ) (τ : ℝ → A ≃⋆ₐ[ℂ] A) (Dip Cur : Fin 3 → A)
    (hM : IsLongWaveModel ω τ Dip Cur) (hbar V : ℝ) (hhbar : 0 < hbar) (hV : 0 < V) :
    ∀ t : ℝ,
      (sigmaCorr ω τ hbar V Dip Cur t).im = 0 ∧ (phiCorr ω τ hbar V Cur t).im = 0 := by sorry

end Arxiv1003_4724
