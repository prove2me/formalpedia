-- Prove2me | Theorems.Thm_AutomorphicForm_integrable_and_differentiableAt_and_continuous_godementSection_of_mem_schwartzBruhat2
-- name    : AutomorphicForm.integrable_and_differentiableAt_and_continuous_godementSection_of_mem_schwartzBruhat2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/0dd72bb5-09ff-53a4-a128-3111fa960b23
-- title:
--   Godement section: convergence, holomorphy and continuity for Re s>0
-- statement:
--   Let $F$ be a number field, and equip the idele group $(\mathbb{A}_F)^\times = (\mathrm{AdeleRing}(\mathcal{O}_F,F))^\times$ with a measurable structure that is the Borel structure of its topology; let $\nu_0$ be a Haar measure on it. Let $\mu,\nu\colon(\mathbb{A}_F)^\times\to\mathbb{C}^\times$ be group homomorphisms satisfying $\lVert\mu(x)\rVert=\lVert\nu(x)\rVert=1$ for all $x$, with $x\mapsto\mu(x)$ and $x\mapsto\nu(x)$ continuous as $\mathbb{C}$-valued functions, and let $\alpha\colon(\mathbb{A}_F)^\times\to\mathbb{R}^\times$ be a homomorphism with $\alpha(x)>0$ for all $x$ and $\alpha(x)=\lVert x\rVert$, the idele norm being defined as the value of the distributive Haar character of $\mathbb{A}_F$ at $x$. Let $\Phi\colon\mathbb{A}_F^2\to\mathbb{C}$ lie in `schwartzBruhat2 F`, the $\mathbb{C}$-span of the products of a Schwartz function of the two archimedean (mixed-space) coordinates with a locally constant, compactly supported function of the two finite-adelic coordinates. Write $f(s,g)=\mu(\det g)\,\alpha(\det g)^{s+1/2}\int_{(\mathbb{A}_F)^\times}\Phi(t\cdot(g_{1,0},g_{1,1}))\,(\mu\nu^{-1})(t)\,\lVert t\rVert^{2s+1}\,d\nu_0(t)$ for $g\in\mathrm{GL}_2(\mathbb{A}_F)$, the integral being a Bochner integral. Then four assertions hold: for all $g$ and all $s$ with $\operatorname{Re} s>0$ the above integrand is $\nu_0$-integrable; for each $g$ the function $s\mapsto f(s,g)$ is complex differentiable at each $s$ with $\operatorname{Re} s>0$; $(s,g)\mapsto f(s,g)$ is continuous on $\{\operatorname{Re} s>0\}\times\mathrm{GL}_2(\mathbb{A}_F)$; and for each fixed $s$ with $\operatorname{Re} s>0$ the function $g\mapsto f(s,g)$ is continuous.
--
--   This is the basic analytic input on Godement sections attached to adelic Schwartz–Bruhat functions of two variables: absolute convergence of the associated global zeta integral in the half-plane $\operatorname{Re} s>0$, holomorphy in the spectral parameter, and joint continuity in $(s,g)$. It supports the meromorphic continuation of the Weyl intertwining integral and the Rankin–Selberg computations used in the Langlands–Tunnell part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrable_and_differentiableAt_and_continuous_godementSection_of_mem_schwartzBruhat2.lean

import Definitions.Def_AutomorphicForm_GodementSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.TateGlobal AutomorphicForm

theorem AutomorphicForm.integrable_and_differentiableAt_and_continuous_godementSection_of_mem_schwartzBruhat2
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure]
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
    (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
    (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (_hαN : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm F x)
    (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (_hΦ : Φ ∈ schwartzBruhat2 F) :
    (∀ (g : AdelicGL2 (𝓞 F) F) (s : ℂ), 0 < s.re →
      Integrable (fun t : (AdeleRing (𝓞 F) F)ˣ =>
        Φ (bottomRowVec F g (t : AdeleRing (𝓞 F) F)) * (((μ * ν⁻¹) t : ℂˣ) : ℂ)
          * ((ideleNorm F t : ℝ) : ℂ) ^ (2 * s + 1)) ν₀) ∧
    (∀ (g : AdelicGL2 (𝓞 F) F) (s : ℂ), 0 < s.re →
      DifferentiableAt ℂ (fun s : ℂ => godementSection F ν₀ μ ν α hα Φ s g) s) ∧
    ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => godementSection F ν₀ μ ν α hα Φ p.1 p.2)
      {p | 0 < p.1.re} ∧
    (∀ s : ℂ, 0 < s.re →
      Continuous fun g : AdelicGL2 (𝓞 F) F => godementSection F ν₀ μ ν α hα Φ s g) := by sorry
