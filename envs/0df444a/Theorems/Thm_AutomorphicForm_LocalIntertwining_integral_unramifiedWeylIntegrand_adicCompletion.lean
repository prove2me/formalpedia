-- Prove2me | Theorems.Thm_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion
-- name    : AutomorphicForm.LocalIntertwining.integral_unramifiedWeylIntegrand_adicCompletion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/0d7c6980-55cf-558d-b583-8fc65e5da262
-- title:
--   Unramified rank-one intertwining integral at a finite place
-- statement:
--   Let $F$ be a number field, $v$ a nonzero prime of $\mathcal{O}_F$ (a point of the height-one spectrum), $F_v$ the $v$-adic completion equipped with its Borel $\sigma$-algebra, and $\mu$ an additive Haar measure on $F_v$. Let $\varpi \in F_v^{\times}$ satisfy $\mathrm{v}(\varpi) = \mathrm{ofAdd}(-1)$, i.e. $\varpi$ is a uniformiser for the normalised valuation, and let $\chi : F_v^{\times} \to \mathbb{C}^{\times}$ be a group homomorphism with $\chi(u) = 1$ whenever $\mathrm{v}(u) = 1$, so $\chi$ is unramified. Let $s \in \mathbb{C}$ satisfy $\lVert \chi(\varpi)\, N(v)^{-2s} \rVert < 1$, where $N(v)$ is the absolute norm of the ideal $v$ and the power is the principal complex power. Then the integral over $F_v$, with respect to $\mu$, of the function equal to $1$ on the valuation ring $\mathcal{O}_v$ and equal to $\chi(y)^{-1} \cdot m(y)^{-(2s+1)}$ off $\mathcal{O}_v$ — here $\chi^{-1}$ is extended by $0$ at $0$, and $m(y)$ is the module of the scaling action of $y$ on the Haar measure of $F_v$, set to $0$ at $y = 0$ — equals $$\mu(\mathcal{O}_v)\,\bigl(1 - \chi(\varpi) N(v)^{-(2s+1)}\bigr)\bigl(1 - \chi(\varpi) N(v)^{-2s}\bigr)^{-1},$$ with $\mu(\mathcal{O}_v)$ the real-valued measure of $\mathcal{O}_v$ cast into $\mathbb{C}$.
--
--   This is the rank-one Gindikin–Karpelevich computation at a finite place: the local intertwining integral on the spherical vector of an unramified principal series evaluates to $\mu(\mathcal{O}_v)\,L(2s,\chi)/L(2s+1,\chi)$ for the unramified local Euler factor $L(w,\chi) = (1-\chi(\varpi)N(v)^{-w})^{-1}$. It feeds the adelic product formula for the Weyl intertwining integral and hence the analytic continuation of the normalised intertwining operator on induced sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean

import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem AutomorphicForm.LocalIntertwining.integral_unramifiedWeylIntegrand_adicCompletion
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1) :
    ∫ x, ((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x) ∂μ
      = (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)
          * (1 - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))
          * (1 - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s)))⁻¹ := by sorry
