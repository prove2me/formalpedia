-- Prove2me | Theorems.Thm_EisensteinGeneral_LocalUnr_integral_twisted_eq
-- name    : EisensteinGeneral.LocalUnr.integral_twisted_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/86ac5fa0-e618-5478-847e-ca7c887bfbb6
-- title:
--   Twisted unramified intertwining integral as a finite geometric sum
-- statement:
--   Let $F$ be a number field, $v$ a nonzero prime of $\mathcal{O}_F$, and let $K_v$ denote the completion of $F$ at $v$, equipped with a measurable structure compatible with its Borel structure, and let $\mu$ be an additive Haar measure on $K_v$; write $q =$ `Ideal.absNorm v.asIdeal` for the absolute norm of the prime and $\mathcal{O}_v$ for the valuation subring `v.adicCompletionIntegers F`. Let $\varpi \in K_v^\times$ satisfy $\mathrm{v}(\varpi) = \mathrm{ofAdd}(-1)$, let $\chi \colon K_v^\times \to \mathbb{C}^\times$ be a group homomorphism with $\chi(u) = 1$ whenever $\mathrm{v}(u) = 1$, and let $s \in \mathbb{C}$ satisfy $\lVert \chi(\varpi) q^{-2s}\rVert < 1$. Let $\psi$ be an additive character of $K_v$ with values in $\mathbb{C}$ and $n \in \mathbb{Z}$ such that $\psi$ is trivial on $\{x : \mathrm{v}(x) \le \exp n\}$ while some $x$ with $\mathrm{v}(x) \le \exp(n+1)$ has $\psi(x) \ne 1$. Let $\xi \in K_v$ and $M \in \mathbb{N}$ with $\mathrm{v}(\xi) = \exp(n - M)$. Then the integral against $\mu$ of $x \mapsto g(x)\,\psi(-(\xi x))$, where $g$ is $1$ on $\mathcal{O}_v$ and, off $\mathcal{O}_v$, is $\chi^{-1}$ evaluated at $x$ (as a unit, the value $0$ being taken at $x=0$) times $\mathrm{modulus}(x)^{-(2s+1)}$, with $\mathrm{modulus}(x)$ the scaling factor of multiplication by $x$ on Haar measure, equals
--   $$\mu_{\mathbb{R}}(\mathcal{O}_v)\,\bigl(1 - \chi(\varpi) q^{-(2s+1)}\bigr) \sum_{k=0}^{M} \bigl(\chi(\varpi) q^{-2s}\bigr)^{k}.$$
--
--   This is the local intertwining integrand of $\mathrm{GL}_2$ at an unramified place, twisted by an additive character $\psi$ of exact level $n$ and evaluated at a twisting parameter $\xi$ of valuation $M - n$: the twist truncates the geometric series of [`AutomorphicForm.LocalIntertwining.integral_unramifiedWeylIntegrand_adicCompletion`](thm.html#AutomorphicForm.LocalIntertwining.integral_unramifiedWeylIntegrand_adicCompletion) to its first $M+1$ terms. It is used in the computation of the Whittaker coefficients of Bruhat–Eisenstein series, where the local factors are assembled into an Euler product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinGeneral_LocalUnr_integral_twisted_eq.lean

import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem EisensteinGeneral.LocalUnr.integral_twisted_eq
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1)
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (ξ : v.adicCompletion F) (M : ℕ) (hξ : Valued.v ξ = WithZero.exp (n - (M : ℤ))) :
    ∫ x, (((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
          * ψ (-(ξ * x))) ∂μ
      = (μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℂ)
          * (1 - ((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))
          * ∑ k ∈ Finset.range (M + 1),
              (((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))) ^ k := by sorry
