-- Prove2me | Theorems.Thm_AutomorphicForm_exists_entire_eq_godementEisenstein_fe_norm_le_of_mem_schwartzBruhat2
-- name    : AutomorphicForm.exists_entire_eq_godementEisenstein_fe_norm_le_of_mem_schwartzBruhat2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/75aab664-e05c-5363-8104-8bfd1b807404
-- title:
--   Godement Eisenstein series: continuation, functional equation, strip bounds
-- statement:
--   Let $F$ be a number field, with adele ring $\mathbb{A}_F$ and idele group $\mathbb{A}_F^{\times}$ carried with their Borel measurable structures; fix a Haar measure $\nu_0$ on $\mathbb{A}_F^{\times}$, an additive Haar measure $\mu_1$ on $\mathbb{A}_F$ with $\mu_1(\mathrm{adelicBox}\,F)=1$, and an additive character $\psi$ of $\mathbb{A}_F$ into $\mathbb{C}$ satisfying `IsPrincipalInvariantAddChar`, continuous and non-trivial. Let $\alpha\colon\mathbb{A}_F^{\times}\to\mathbb{R}^{\times}$ be the character obtained from `distribHaarChar` of $\mathbb{A}_F$ by mapping $\mathbb{R}_{\ge 0}$ into $\mathbb{R}$ and passing to units, assumed pointwise positive and equal to $1$ on ideles coming from $F^{\times}$. Let $\mu,\nu\colon\mathbb{A}_F^{\times}\to\mathbb{C}^{\times}$ be continuous characters of absolute value $1$ which are trivial on the image of $F^{\times}$, and let $\Phi$ lie in the $\mathbb{C}$-span of the pure tensors `pureTensorSet2` $F$ in functions $(\mathrm{Fin}\,2\to\mathbb{A}_F)\to\mathbb{C}$. Put $f_s(g)=\mu(\det g)\,\alpha(\det g)^{s+1/2}\,Z_{\nu_0}\bigl(t\mapsto\Phi(\text{bottom row of }g\text{ at }t),\mu\nu^{-1},2s+1\bigr)$ (`godementSection`), and $f'$ the same expression with $\mu,\nu$ interchanged and $\Phi$ replaced by $x\mapsto\widehat{\Phi}^{\psi,\mu_1}(x_1,-x_0)$ (`reflectPair`); let $E_s(g)=f_s(g)+\sum_{\xi\in F}f_s(w\,n(\xi)g)$ and likewise $E'$, with $w$ the adelic Weyl element and $n(\xi)$ the upper unipotent matrix. The conclusion is a conjunction. First: if $\mu\nu^{-1}\neq\lvert\cdot\rvert^{i\tau}$ (`normPowChar` $F\,\tau$) for every real $\tau$, there exist $H,H'\colon\mathbb{C}\to GL_2(\mathbb{A}_F)\to\mathbb{C}$, entire in $s$ for each $g$, jointly continuous in $(s,g)$, with $H_s=E_s$ and $H'_s=E'_s$ for $\operatorname{Re}s>1/2$, satisfying $H_s(g)=H'_{-s}(g)$ for all $s,g$, and such that for all reals $\sigma_1,\sigma_2,c,u$ with $c>0$ and every $t\in GL_2(\mathbb{A}_F)$ there are $A\in\mathbb{R}$, $N\in\mathbb{N}$ with $\lVert H_s(gt)\rVert\le A(1+\lvert\operatorname{Im}s\rvert)^N(1+\mathrm{archHeight}_F(g_\infty))^N$ for $\sigma_1\le\operatorname{Re}s\le\sigma_2$ and $g$ in the integral windowed Siegel set of parameters $c,u$, and the same bound for $H'$. Second: for every real $\tau$ with $\mu\nu^{-1}=\lvert\cdot\rvert^{i\tau}$, the same list holds with the two interpolation clauses replaced by $H_s(g)=\bigl(s-\tfrac{1-i\tau}{2}\bigr)\bigl(s+\tfrac{1+i\tau}{2}\bigr)E_s(g)$ and $H'_s(g)=\bigl(s-\tfrac{1+i\tau}{2}\bigr)\bigl(s+\tfrac{1-i\tau}{2}\bigr)E'_s(g)$ for $\operatorname{Re}s>1/2$.
--
--   This is the analytic input on Eisenstein series attached to Godement sections of Schwartz–Bruhat functions on $\mathbb{A}_F^2$: meromorphic continuation in the spectral parameter with at most the two explicit poles cleared by the displayed quadratic factor, the functional equation relating the series of $\Phi$ at $(\mu,\nu)$ to that of its partial Fourier reflection at $(\nu,\mu)$, and bounds polynomial in $\lvert\operatorname{Im}s\rvert$ and in the archimedean height, uniform on vertical strips and on translated windowed Siegel sets. It is used in the continuation of the Weyl intertwining integral in the Rankin–Selberg part of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_entire_eq_godementEisenstein_fe_norm_le_of_mem_schwartzBruhat2.lean

import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_AutomorphicForm_WindowedSiegelSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal

theorem
    AutomorphicForm.exists_entire_eq_godementEisenstein_fe_norm_le_of_mem_schwartzBruhat2
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν₀ : Measure (AdeleRing (𝓞 F) F)ˣ) [ν₀.IsHaarMeasure]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ₁ : Measure (AdeleRing (𝓞 F) F)) [μ₁.IsAddHaarMeasure]
    (_hμ₁ : μ₁ (adelicBox F) = 1)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (_hψ : IsGlobalAddChar F ψ) :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (_hprin : IsPrincipalTrivial (R := 𝓞 F) (K := F) α)
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (Φ : (Fin 2 → AdeleRing (𝓞 F) F) → ℂ) (_hΦ : Φ ∈ schwartzBruhat2 F),
    let f : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s g => godementSection F ν₀ μ ν α hα Φ s g
    let f' : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s g => godementSection F ν₀ ν μ α hα (reflectPair ψ μ₁ Φ) s g
    let E : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s g =>
      f s g + ∑' ξ : F, f s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)
    let E' : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s g =>
      f' s g + ∑' ξ : F, f' s (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)
    ((∀ τ : ℝ, μ * ν⁻¹ ≠ NumberField.TateGlobal.normPowChar F τ) →
      ∃ H H' : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
        (∀ g : AdelicGL2 (𝓞 F) F, Differentiable ℂ (fun s : ℂ => H s g)) ∧
        (∀ g : AdelicGL2 (𝓞 F) F, Differentiable ℂ (fun s : ℂ => H' s g)) ∧
        (Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => H p.1 p.2) ∧
        (Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => H' p.1 p.2) ∧
        (∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
          H s g = E s g) ∧
        (∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
          H' s g = E' s g) ∧
        (∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), H s g = H' (-s) g) ∧
        (∀ (σ₁ σ₂ c u : ℝ) (t : AdelicGL2 (𝓞 F) F), 0 < c →
          ∃ (A : ℝ) (N : ℕ), ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
            ∀ g ∈ integralWindowedSiegelSet F c u,
              ‖H s (g * t)‖ ≤ A * (1 + |s.im|) ^ N * (1 + archHeight F (glArch (𝓞 F) F g)) ^ N) ∧
        (∀ (σ₁ σ₂ c u : ℝ) (t : AdelicGL2 (𝓞 F) F), 0 < c →
          ∃ (A : ℝ) (N : ℕ), ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
            ∀ g ∈ integralWindowedSiegelSet F c u,
              ‖H' s (g * t)‖ ≤ A * (1 + |s.im|) ^ N * (1 + archHeight F (glArch (𝓞 F) F g)) ^ N)) ∧
    (∀ τ : ℝ, μ * ν⁻¹ = NumberField.TateGlobal.normPowChar F τ →
      ∃ H H' : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
        (∀ g : AdelicGL2 (𝓞 F) F, Differentiable ℂ (fun s : ℂ => H s g)) ∧
        (∀ g : AdelicGL2 (𝓞 F) F, Differentiable ℂ (fun s : ℂ => H' s g)) ∧
        (Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => H p.1 p.2) ∧
        (Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => H' p.1 p.2) ∧
        (∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
          H s g = (s - ((1 : ℂ) - (τ : ℂ) * Complex.I) / 2) * (s + ((1 : ℂ) + (τ : ℂ) * Complex.I) / 2) * E s g) ∧
        (∀ s : ℂ, (1 / 2 : ℝ) < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
          H' s g = (s - ((1 : ℂ) + (τ : ℂ) * Complex.I) / 2) * (s + ((1 : ℂ) - (τ : ℂ) * Complex.I) / 2) * E' s g) ∧
        (∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), H s g = H' (-s) g) ∧
        (∀ (σ₁ σ₂ c u : ℝ) (t : AdelicGL2 (𝓞 F) F), 0 < c →
          ∃ (A : ℝ) (N : ℕ), ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
            ∀ g ∈ integralWindowedSiegelSet F c u,
              ‖H s (g * t)‖ ≤ A * (1 + |s.im|) ^ N * (1 + archHeight F (glArch (𝓞 F) F g)) ^ N) ∧
        (∀ (σ₁ σ₂ c u : ℝ) (t : AdelicGL2 (𝓞 F) F), 0 < c →
          ∃ (A : ℝ) (N : ℕ), ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ σ₂ →
            ∀ g ∈ integralWindowedSiegelSet F c u,
              ‖H' s (g * t)‖ ≤ A * (1 + |s.im|) ^ N * (1 + archHeight F (glArch (𝓞 F) F g)) ^ N)) := by sorry
