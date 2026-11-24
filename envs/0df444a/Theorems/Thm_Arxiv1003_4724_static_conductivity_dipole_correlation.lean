-- Prove2me | Theorems.Thm_Arxiv1003_4724_static_conductivity_dipole_correlation
-- name    : Arxiv1003_4724.static_conductivity_dipole_correlation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T23:57:35.332131+00:00
-- url     : https://prove2.me/theorems/8a23162b-4618-4907-860f-ef43bd4f0a04
-- title:
--   Eq. (33): the static conductivity as a long-time limit of current and dipole correlations
-- statement:
--   In a long-wavelength model with $\hbar,V>0$, let $\sigma(t)$ be the current-dipole correlation function of eq. (31), integrable on $(0,\infty)$. Let $\sigma^{(0)}(\omega)=\int_0^\infty e^{i\omega t}\sigma(t)\,dt$ (eq. 30). Let the static conductivity $\sigma_{st}\ge0$ be its low-frequency limit, $\sigma_{st}=\lim_{\omega\to0}\sigma^{(0)}(\omega)$ (eqs. 14, 24, 29). Then
--
--   $$\lim_{t\to\infty}\int_0^t\sigma(t')\,dt'=\sigma_{st}=\lim_{t\to\infty}\frac{i}{3\hbar V}\langle[P^\beta(t),P^\beta(0)]\rangle .$$
--
--   So the static conductivity is the long-time limit of the dipole commutator.
--
--   **Formalization Note** The paper's definition (14) of $\sigma_{st}$, an iterated limit of $\sigma(q,\omega)$, is linked to Sec. III through (24) and (29). Here it is encoded as the hypothesis $\sigma^{(0)}(\omega)\to\sigma_{st}$ as $\omega\to0$, $\omega\ne0$. The integral (30) is read as an absolutely convergent (Lebesgue) integral, so $\sigma$ is assumed integrable on $(0,\infty)$.
-- source:
--   Bobrov, Trigger, van Heijst and Schram, Kramers-Kronig relations for the dielectric function and the static conductivity of Coulomb systems, arXiv:1003.4724v1 (2010), claim c009; Sec. III, eq. (33) from eqs. (29)-(31) and (26), PDF p. 7

import Mathlib
import Definitions.Def_Arxiv1003_4724_Basic

open MeasureTheory Filter Topology

namespace Arxiv1003_4724

theorem static_conductivity_dipole_correlation {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A]
    (ω : A →ₗ[ℂ] ℂ) (τ : ℝ → A ≃⋆ₐ[ℂ] A) (Dip Cur : Fin 3 → A)
    (hM : IsLongWaveModel ω τ Dip Cur) (hbar V : ℝ) (hhbar : 0 < hbar) (hV : 0 < V)
    (sigmaSt : ℝ) (hsig : 0 ≤ sigmaSt)
    (hint : IntegrableOn (sigmaCorr ω τ hbar V Dip Cur) (Set.Ioi 0))
    (h14 : Tendsto (sigma0 ω τ hbar V Dip Cur) (𝓝[≠] (0 : ℝ)) (𝓝 (sigmaSt : ℂ))) :
    Tendsto (fun t : ℝ => ∫ s in (0 : ℝ)..t, sigmaCorr ω τ hbar V Dip Cur s) atTop
        (𝓝 (sigmaSt : ℂ)) ∧
      Tendsto (dipoleCorr ω τ hbar V Dip) atTop (𝓝 (sigmaSt : ℂ)) := by sorry

end Arxiv1003_4724
