-- Prove2me | Theorems.Thm_Arxiv1003_4724_true_dielectric_dipole_limit
-- name    : Arxiv1003_4724.true_dielectric_dipole_limit
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T23:58:23.455116+00:00
-- url     : https://prove2.me/theorems/9fa36f23-22f6-4add-a697-542a384f9e6f
-- title:
--   Eq. (38): in the true-dielectric limit the long-time dipole commutator tends to zero
-- statement:
--   Consider a family of long-wavelength models indexed by a parameter $l$, with a limit along a non-trivial filter $F$ on the parameters (for instance a limit in temperature, density or volume). Each model has its own state, evolution, dipole and current operators, number operators $N_{l,a}$, temperature $T_l>0$ and volume $V_l>0$, with fixed $\hbar>0$, charges $z_ae$ and $e>0$. Each model satisfies the hypotheses of eq. (33): $\sigma_l(t)$ is integrable, and $\sigma_{st}(l)\ge0$ is the low-frequency limit of $\sigma^{(0)}_l$. Assume that along $F$ the system becomes a "true" dielectric (eqs. 36, 37):
--
--   $$\frac{4\pi\langle Z^2\rangle_l}{T_lV_l}\to0,\qquad \sigma_{st}(l)\to0 .$$
--
--   Then for each $l$ the long-time limit $D_l=\lim_{t\to\infty}\frac{i}{3\hbar V_l}\langle[P^\beta(t),P^\beta(0)]\rangle_l$ exists, and $D_l\to0$ along $F$ (eq. 38).
--
--   **Formalization Note** The paper's "$\to0$" does not name the varying parameter. It is formalized as a limit along an arbitrary non-trivial filter on an index set, over one fixed algebra of observables. The condition $\kappa\to0$ of (36) is the same as (37), since $\kappa=\sqrt{\kappa^2}\ge0$. As in the paper's argument, the conclusion follows from (33) and $\sigma_{st}\to0$ alone; hypothesis (37) is kept for fidelity but is not used.
-- source:
--   Bobrov, Trigger, van Heijst and Schram, Kramers-Kronig relations for the dielectric function and the static conductivity of Coulomb systems, arXiv:1003.4724v1 (2010), claim c014; Sec. IV, eq. (38) from eqs. (33), (36), (37), PDF p. 8

import Mathlib
import Definitions.Def_Arxiv1003_4724_Basic

open MeasureTheory Filter Topology

namespace Arxiv1003_4724

theorem true_dielectric_dipole_limit {A ι Par : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] [Fintype ι] (F : Filter Par) [F.NeBot]
    (ω : Par → A →ₗ[ℂ] ℂ) (τ : Par → ℝ → A ≃⋆ₐ[ℂ] A) (Dip Cur : Par → Fin 3 → A)
    (hM : ∀ l, IsLongWaveModel (ω l) (τ l) (Dip l) (Cur l))
    (N : Par → ι → A) (hN : ∀ l a, IsSelfAdjoint (N l a)) (z : ι → ℝ) (e hbar : ℝ)
    (he : 0 < e) (hhbar : 0 < hbar) (T V : Par → ℝ) (hT : ∀ l, 0 < T l) (hV : ∀ l, 0 < V l)
    (sigmaSt : Par → ℝ) (hsig : ∀ l, 0 ≤ sigmaSt l)
    (hint : ∀ l, IntegrableOn (sigmaCorr (ω l) (τ l) hbar (V l) (Dip l) (Cur l)) (Set.Ioi 0))
    (h14 : ∀ l, Tendsto (sigma0 (ω l) (τ l) hbar (V l) (Dip l) (Cur l)) (𝓝[≠] (0 : ℝ))
      (𝓝 (sigmaSt l : ℂ)))
    (h37 : Tendsto (fun l => kappaSq (ω l) (N l) z e (T l) (V l)) F (𝓝 0))
    (h36 : Tendsto sigmaSt F (𝓝 0)) :
    ∃ D : Par → ℂ, (∀ l, Tendsto (dipoleCorr (ω l) (τ l) hbar (V l) (Dip l)) atTop (𝓝 (D l))) ∧
      Tendsto D F (𝓝 0) := by sorry

end Arxiv1003_4724
