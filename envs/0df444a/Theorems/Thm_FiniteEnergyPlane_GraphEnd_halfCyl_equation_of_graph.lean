-- Prove2me | Theorems.Thm_FiniteEnergyPlane_GraphEnd_halfCyl_equation_of_graph
-- name    : FiniteEnergyPlane.GraphEnd.halfCyl_equation_of_graph
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T15:30:50.134437+00:00
-- url     : https://prove2.me/theorems/6326c77b-1068-45f1-be6a-5a372ebafd1c
-- title:
--   Normal coordinates of a holomorphic map over a complex graph solve a Cauchy–Riemann type equation on the cylinder
-- statement:
--   Let $\rho > 0$ and let $\bar J : \mathbb{C} \times \mathbb{C} \to \mathrm{End}_{\mathbb{R}}(\mathbb{C} \times \mathbb{C})$ be $C^\infty$ on $\mathbb{C} \times B_\rho(0)$ with $\bar J^2 = -1$ there. Let $\beta$ be a bump function around $0 \in \mathbb{C}$ and $r_1 < \rho$ with $\beta.\mathrm{rOut} \le \rho$. Let $g, \psi, v : \mathbb{C} \to \mathbb{C}$ be $C^\infty$ with $|g| \le r_1$, $|v| \le r_1$, and suppose the graph of $g$ is $\bar J$-complex:
--   $$\big[\bar J(x, g(x))\,(e, Dg(x)e)\big]_2 = Dg(x)\,\big[\bar J(x, g(x))\,(e, Dg(x)e)\big]_1 \qquad (x, e \in \mathbb{C}).$$
--   The frame $P = $ `Pf`, the normal coordinate $\zeta = $ `ζf` $= P\,(v - g \circ \psi)$, the coefficient matrix $S = $ `Sf` and the cylinder vector $w = $ `wf` are those of the module `FiniteEnergyPlane_GraphEnd`, with $z = e^{2\pi(s+it)}$ (`cylInf s t`).
--
--   **Theorem.** Assume moreover $r_1 \le \beta.\mathrm{rIn}$ and that $u = (\psi, v)$ is $\bar J$-holomorphic, $Du_z \circ i = \bar J(u(z))\,Du_z$. Then
--   1. every $P_z$ is injective;
--   2. $\zeta$ is $C^\infty$, and every $z_0$ has a neighbourhood $B_r(z_0)$ and a constant $M$ with
--   $$\big|\partial_x \zeta(z) + i\,\partial_y \zeta(z)\big| \le M\,|\zeta(z)| \qquad (z \in B_r(z_0));$$
--   3. the entries of $S(s, t)$ are $C^\infty$ and $S(s, t+1) = S(s, t)$;
--   4. $w$ is a half-cylinder solution of $\partial_s w + J_0\,\partial_t w + S\,w = 0$ (`IsHalfCylSolution`), and $w(s, t)$, read as a complex number, equals $\zeta(e^{2\pi(s+it)})$.
--
--   **Role.** This is the equation satisfied by the vertical difference of a holomorphic map and a complex graph, written in the frame-normalised coordinates on the cylindrical end at $\infty$; it holds for any such pair inside the tube, with no asymptotic assumption.
--
--   **Formalization Note.** Item 2 is stated for $y \mapsto P_y(v(y) - g(\psi(y)))$, which is `ζf` unfolded; item 4 uses `vecToC`.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Section 6 (difference of two complex graphs in a standard tube, cf. Lemma 6.20); cylinder conventions of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Ch. 4

import Definitions.Def_FiniteEnergyPlane_GraphEnd

namespace FiniteEnergyPlane.GraphEnd

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `Jbar` be a smooth structure field on `ℂ × ball 0 ρ` with `Jbar² = -1`, `β` a bump around
`0 ∈ ℂ` with `r₁ ≤ β.rIn` and `β.rOut ≤ ρ`, `g : ℂ → ℂ` a smooth map with `‖g‖ ≤ r₁` whose graph
is `Jbar`-complex, and `z ↦ (ψ z, v z)` a smooth `Jbar`-holomorphic map with `‖v‖ ≤ r₁`. Then each
frame `Pf z` is injective, the normal coordinate `ζf = Pf (v - g ∘ ψ)` is smooth with
`|∂ₛζ + i ∂ₜζ| ≤ M |ζ|` locally, the matrix `Sf` is smooth and `1`-periodic in `t`, and the cylinder
vector `wf` solves `∂ₛw + J₀ ∂ₜw + Sf w = 0` with `wf (s, t) = ζf (cylInf s t)`. -/
theorem halfCyl_equation_of_graph (ρ r₁ : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (hJ : ContDiffOn ℝ ∞ Jbar (Set.univ ×ˢ ball (0 : ℂ) ρ))
    (hsq : ∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
      (Jbar p).comp (Jbar p) = -ContinuousLinearMap.id ℝ (ℂ × ℂ))
    (β : ContDiffBump (0 : ℂ)) (hrIn : r₁ ≤ β.rIn) (hrOut : β.rOut ≤ ρ) (hr₁ : r₁ < ρ)
    (g ψ v : ℂ → ℂ) (hg : ContDiff ℝ ∞ g) (hψ : ContDiff ℝ ∞ ψ) (hv : ContDiff ℝ ∞ v)
    (hgr : ∀ x, ‖g x‖ ≤ r₁) (hvr : ∀ z, ‖v z‖ ≤ r₁)
    (hgJ : ∀ x e : ℂ, (Jbar (x, g x) (e, fderiv ℝ g x e)).2 =
      fderiv ℝ g x (Jbar (x, g x) (e, fderiv ℝ g x e)).1)
    (hhol : ∀ z, (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z).comp
        (Complex.I • ContinuousLinearMap.id ℝ ℂ) =
      (Jbar (ψ z, v z)).comp (fderiv ℝ (fun x : ℂ => (ψ x, v x)) z)) :
    (∀ z, Function.Injective (Pf Jbar β g ψ z)) ∧
      ContDiff ℝ ∞ (ζf Jbar β g ψ v) ∧
      (∀ z₀ : ℂ, ∃ r > (0 : ℝ), ∃ M : ℝ, ∀ z ∈ ball z₀ r,
        ‖fderiv ℝ (fun y => Pf Jbar β g ψ y (v y - g (ψ y))) z 1 +
            Complex.I * fderiv ℝ (fun y => Pf Jbar β g ψ y (v y - g (ψ y))) z Complex.I‖ ≤
          M * ‖Pf Jbar β g ψ z (v z - g (ψ z))‖) ∧
      (∀ i j, ContDiff ℝ ∞ (fun p : ℝ × ℝ => Sf Jbar β g ψ v p i j)) ∧
      (∀ s t : ℝ, Sf Jbar β g ψ v (s, t + 1) = Sf Jbar β g ψ v (s, t)) ∧
      IsHalfCylSolution (Sf Jbar β g ψ v) (wf Jbar β g ψ v) ∧
      ∀ s t : ℝ, vecToC (wf Jbar β g ψ v (s, t)) = ζf Jbar β g ψ v (cylInf s t) := by
  sorry

end FiniteEnergyPlane.GraphEnd
