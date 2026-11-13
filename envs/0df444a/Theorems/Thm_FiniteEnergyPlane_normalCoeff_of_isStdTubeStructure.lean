-- Prove2me | Theorems.Thm_FiniteEnergyPlane_normalCoeff_of_isStdTubeStructure
-- name    : FiniteEnergyPlane.normalCoeff_of_isStdTubeStructure
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-12T18:17:14.427294+00:00
-- url     : https://prove2.me/theorems/6f9e3be9-f8cb-432f-bdea-c0b1335f9abc
-- title:
--   The normal coefficient of a standard tube structure
-- statement:
--   Let $\rho, b > 0$ and let $(\bar J, J_\infty, S_\infty)$ be a standard tube structure (`IsStdTubeStructure ρ b Jbar Jinf Sinf`). Let $N(s,t) =$ `normalCoeff Jbar (s, t)` be the real $2\times 2$ matrix of $a \mapsto \big[(\partial_w \bar J(z, 0)\,a)(2\pi i z, 0)\big]_2$ at $z = e^{2\pi(s+it)}$. Then:
--   1. every entry of $N$ is $C^\infty$ on $\mathbb{R}^2$, and $N(s, t+1) = N(s, t)$;
--   2. every entry of $S_\infty$ is $C^\infty$;
--   3. $N$ is exponentially asymptotic to $S_\infty$ at rate $b$ as $s \to +\infty$ (`IsExpAsymptoticTo (normalCoeff Jbar) Sinf b`);
--   4. $N$ is the pull-back of a smooth zero-order term on the plane (`IsPlaneCoeff`): $N(s,t)\,a = 4\pi\bar z\,A(z)\,a$ for a $C^\infty$ map $A : \mathbb{C} \to \mathrm{End}_{\mathbb{R}}(\mathbb{C})$.
--
--   **Role.** $N$ is the zero-order term of the linearization of the $\bar J$-Cauchy–Riemann operator in the normal direction along $\mathbb{C} \times \{0\}$, in cylinder coordinates. The four properties are the hypotheses on the coefficient of a Cauchy–Riemann operator on the cylinder with a removable end at $s = -\infty$ and an asymptotic operator $-J_0\partial_t - S_\infty$ at $s = +\infty$.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Lemmas 6.10 and 6.20 (families of fast planes); operators in the setting of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Ch. 4

import Definitions.Def_FiniteEnergyPlane_TubeFamily

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology CauchyRiemannIndex
open scoped ContDiff ENNReal Real

/-- For a standard tube structure, the normal coefficient `normalCoeff Jbar` is smooth,
`1`-periodic in `t`, exponentially asymptotic to `Sinf` at rate `b`, and the pull-back of a smooth
zero-order term on the plane (`IsPlaneCoeff`); `Sinf` is smooth. -/
theorem normalCoeff_of_isStdTubeStructure (ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → Mat 1) (hstd : IsStdTubeStructure ρ b Jbar Jinf Sinf) :
    (∀ i j, ContDiff ℝ ∞ (fun x : ℝ × ℝ => normalCoeff Jbar x i j)) ∧
      (∀ s t : ℝ, normalCoeff Jbar (s, t + 1) = normalCoeff Jbar (s, t)) ∧
      (∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) ∧
      IsExpAsymptoticTo (normalCoeff Jbar) Sinf b ∧
      IsPlaneCoeff (normalCoeff Jbar) := by
  sorry

end FiniteEnergyPlane
