-- Prove2me | Theorems.Thm_Arxiv1003_4724_static_permittivity_exceeds_one
-- name    : Arxiv1003_4724.static_permittivity_exceeds_one
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T23:55:34.74829+00:00
-- url     : https://prove2.me/theorems/c955de56-2dea-46f2-b16e-cc5a93524129
-- title:
--   Eq. (10) at small $q$ (as proved): $\varepsilon(q,0)>1$ for small $q$ when $\langle Z^2\rangle>0$
-- statement:
--   Assume the setting and hypotheses of eq. (23): a state, pairwise commuting self-adjoint number operators $N_a$, charges $z_ae$ with $e>0$, $T,V>0$, quasi-neutrality (3), the long-wavelength relation (18) and the fluctuation identity (22). Assume moreover that the total charge fluctuates, $\langle Z^2\rangle>0$, i.e. $\kappa>0$. Then there is $\delta>0$ such that
--
--   $$\varepsilon(q,0)>1\qquad\text{for all }0<q<\delta .$$
--
--   So at small wave vectors the static permittivity satisfies the inequality (10), $\varepsilon(q,0)>1$, rather than the alternative $\varepsilon(q,0)<0$ of (11).
--
--   **Formalization Note** The paper asserts the inequality "for arbitrary thermodynamic parameters", but its argument, eq. (23), gives it only when $\kappa>0$. For $\kappa=0$, eq. (23) only says $q^2\varepsilon(q,0)\to0$, which allows $\varepsilon(q,0)=1/2$ or $\varepsilon(q,0)=-1$. The hypothesis $\langle Z^2\rangle>0$ is therefore added, and the statement is the one the argument proves. "For small $q$" is formalized as an explicit $\delta$.
-- source:
--   Bobrov, Trigger, van Heijst and Schram, Kramers-Kronig relations for the dielectric function and the static conductivity of Coulomb systems, arXiv:1003.4724v1 (2010), claim c003; Sec. II, text after eq. (23), PDF p. 5; restated in Sec. IV, PDF p. 7; inequality (10), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv1003_4724_Basic

open MeasureTheory Filter Topology

namespace Arxiv1003_4724

theorem static_permittivity_exceeds_one {A ι : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] [Fintype ι]
    (ω : A →ₗ[ℂ] ℂ) (hω : IsState ω) (N : ι → A) (hN : ∀ a, IsSelfAdjoint (N a))
    (hNc : ∀ a b, Commute (N a) (N b)) (z : ι → ℝ) (e T V : ℝ) (he : 0 < e) (hT : 0 < T)
    (hV : 0 < V) (h3 : IsQuasiNeutral ω N z e V) (epsStatic : ℝ → ℝ) (D : ι → ι → ℝ)
    (h18 : Tendsto (fun q => q ^ 2 * epsStatic q) (𝓝[>] (0 : ℝ))
      (𝓝 (4 * Real.pi * ∑ a, ∑ b, z a * z b * e ^ 2 * D a b)))
    (h22 : ∀ a b, ((T * D a b : ℝ) : ℂ) = numberCov ω N a b / V)
    (hZ : 0 < (ω (totalCharge N z e * totalCharge N z e)).re) :
    ∃ δ > 0, ∀ q : ℝ, 0 < q → q < δ → 1 < epsStatic q := by sorry

end Arxiv1003_4724
