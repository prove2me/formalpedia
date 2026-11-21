-- Prove2me | Theorems.Thm_FiniteEnergyPlane_GraphEnd_isExpAsymptoticTo_Sf
-- name    : FiniteEnergyPlane.GraphEnd.isExpAsymptoticTo_Sf
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-20T15:31:44.269924+00:00
-- url     : https://prove2.me/theorems/9259895b-3924-4308-a460-1e6371ec9fbe
-- title:
--   The normal-coordinate coefficient matrix is exponentially asymptotic to the rotated limit loop
-- statement:
--   Let $\rho > 0$ and let $\bar J : \mathbb{C} \times \mathbb{C} \to \mathrm{End}_{\mathbb{R}}(\mathbb{C} \times \mathbb{C})$ be $C^\infty$ on $\mathbb{C} \times B_\rho(0)$ with $\bar J^2 = -1$ there. Let $\beta$ be a bump function around $0 \in \mathbb{C}$ and $r_1 < \rho$ with $\beta.\mathrm{rOut} \le \rho$. Let $g, \psi, v : \mathbb{C} \to \mathbb{C}$ be $C^\infty$ with $|g| \le r_1$, $|v| \le r_1$, and suppose the graph of $g$ is $\bar J$-complex:
--   $$\big[\bar J(x, g(x))\,(e, Dg(x)e)\big]_2 = Dg(x)\,\big[\bar J(x, g(x))\,(e, Dg(x)e)\big]_1 \qquad (x, e \in \mathbb{C}).$$
--   The frame $P = $ `Pf`, the normal coordinate $\zeta = $ `ζf` $= P\,(v - g \circ \psi)$, the coefficient matrix $S = $ `Sf` and the cylinder vector $w = $ `wf` are those of the module `FiniteEnergyPlane_GraphEnd`, with $z = e^{2\pi(s+it)}$ (`cylInf s t`).
--
--   **Theorem.** Assume moreover $r_1 < \beta.\mathrm{rIn}$, that $\bar J$ is a standard tube structure with limits $J_\infty$, $S_\infty$ and rate $b > 0$ (`IsStdTubeStructure ρ b Jbar Jinf Sinf`), that for some $\delta < 0$ the maps $(s, t) \mapsto g(e^{2\pi(s+it)})$ and $(s, t) \mapsto v(e^{2\pi(s+it)})$ decay like $e^{\delta s}$ in $C^\infty$ (`ExpDecayCInfty … (-δ)`), and that $\psi(z)/z - \kappa$ decays at rate $b' > 0$ in the same sense, with $\kappa \ne 0$. Then for every $d$ with
--   $$0 < d < \min(b, b', -\delta)$$
--   the coefficient matrix is exponentially asymptotic to the rotated limit loop,
--   $$S(s, t) - S_\infty\Big(t + \frac{\arg \kappa}{2\pi}\Big) \to 0 \ \text{ like } e^{-ds} \text{ in } C^\infty \qquad (\texttt{IsExpAsymptoticTo}),$$
--   and there is $C$ with $|w(s, t)| \le C\,e^{\delta s}$ for all $s > 0$, $t \in \mathbb{R}$.
--
--   **Role.** These are the asymptotic properties of the end equation of the vertical difference: the operator is asymptotic to the limit asymptotic operator, rotated by the asymptotic phase of $\psi$, and the solution keeps the decay rate of the two maps.
--
--   **Formalization Note.** No holomorphicity of $(\psi, v)$ is assumed here.
-- source:
--   Toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Section 6 (difference of two complex graphs in a standard tube, cf. Lemma 6.20); cylinder conventions of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Ch. 4

import Definitions.Def_FiniteEnergyPlane_GraphEnd

namespace FiniteEnergyPlane.GraphEnd

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `Jbar` be a standard tube structure with limits `Jinf`, `Sinf` and rate `b > 0`, `β` a bump
around `0 ∈ ℂ` with `r₁ < β.rIn` and `β.rOut ≤ ρ`, `g : ℂ → ℂ` a smooth map with `‖g‖ ≤ r₁`, a
`Jbar`-complex graph, with `g ∘ cylInf` decaying like `e^{δ s}` in `C^∞` (`δ < 0`), and `ψ, v`
smooth with `‖v‖ ≤ r₁`, `ψ(z)/z → κ ≠ 0` at rate `b' > 0` and `v ∘ cylInf` decaying like
`e^{δ s}` in `C^∞`. Then `Sf - Sinf(· + arg κ / 2π)` decays like `e^{-d s}` in `C^∞` for every
`0 < d < min(b, b', -δ)`, and `‖wf (s, t)‖ ≤ C e^{δ s}` for `s > 0`. -/
theorem isExpAsymptoticTo_Sf (ρ b : ℝ) (hb : 0 < b)
    (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hT : IsStdTubeStructure ρ b Jbar Jinf Sinf)
    (δ : ℝ) (hδ : δ < 0) (β : ContDiffBump (0 : ℂ)) (r₁ : ℝ) (hr₁ : r₁ < ρ)
    (hrIn : r₁ < β.rIn) (hrOut : β.rOut ≤ ρ)
    (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g) (hgr : ∀ x, ‖g x‖ ≤ r₁)
    (hgJ : ∀ x e : ℂ, (Jbar (x, g x) (e, fderiv ℝ g x e)).2 =
      fderiv ℝ g x (Jbar (x, g x) (e, fderiv ℝ g x e)).1)
    (hgas : ExpDecayCInfty (fun p : ℝ × ℝ => g (cylInf p.1 p.2)) (-δ))
    (ψ v : ℂ → ℂ) (κ : ℂ) (b' : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hv : ContDiff ℝ ∞ v) (hvr : ∀ z, ‖v z‖ ≤ r₁)
    (hκ : κ ≠ 0) (hb' : 0 < b')
    (hψas : ExpDecayCInfty (fun p : ℝ × ℝ => ψ (cylInf p.1 p.2) / cylInf p.1 p.2 - κ) b')
    (hvas : ExpDecayCInfty (fun p : ℝ × ℝ => v (cylInf p.1 p.2)) (-δ)) :
    (∀ d : ℝ, 0 < d → d < min (min b b') (-δ) →
      IsExpAsymptoticTo (Sf Jbar β g ψ v) (fun t => Sinf (t + Complex.arg κ / (2 * π))) d) ∧
      ∃ C : ℝ, ∀ s > 0, ∀ t : ℝ, ‖wf Jbar β g ψ v (s, t)‖ ≤ C * Real.exp (δ * s) := by
  sorry

end FiniteEnergyPlane.GraphEnd
