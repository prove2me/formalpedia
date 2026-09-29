-- Prove2me | Theorems.Thm_EisensteinGeneral_LocalUnr_integral_twisted_eq_zero_of_exp_lt
-- name    : EisensteinGeneral.LocalUnr.integral_twisted_eq_zero_of_exp_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/a516a9bd-c091-5c8c-85a1-03e0265ee4aa
-- title:
--   Vanishing of the twisted unramified local integral off level n
-- statement:
--   Let $F$ be a number field, $v$ a finite place of $F$ (a height-one prime of $\mathcal O_F$) and $K_v$ the $v$-adic completion, equipped with a measurable structure that is the Borel structure of its topology, and let $\mu$ be an additive Haar measure on $K_v$. Assume given: a unit $\varpi\in K_v^\times$ with $\mathrm{v}(\varpi)=\mathrm{ofAdd}(-1)$ (a uniformiser); a monoid homomorphism $\chi\colon K_v^\times\to\mathbb C^\times$ with $\chi(u)=1$ whenever $\mathrm{v}(u)=1$ (unramified, no continuity assumed); a complex number $s$ with $\bigl\|\chi(\varpi)\,N(v)^{-2s}\bigr\|<1$, where $N(v)$ is the absolute norm of the prime ideal of $v$; an additive character $\psi\colon K_v\to\mathbb C$ and an integer $n$ such that $\psi$ is trivial on $\{x:\mathrm{v}(x)\le\exp n\}$ while some $x$ with $\mathrm{v}(x)\le\exp(n+1)$ has $\psi(x)\ne 1$ (so $n$ is the exact level of $\psi$); and $\xi\in K_v$ with $\mathrm{v}(\xi)>\exp n$. Then the $\mu$-integral over $K_v$ of $x\mapsto u(x)\,\psi(-(\xi x))$ vanishes, where $u(x)=1$ for $x$ in the valuation ring $\mathcal O_v$ and, for $x\notin\mathcal O_v$, $u(x)=\chi^{-1}(x)\,|x|^{-(2s+1)}$, with $\chi^{-1}(x)$ the value of $\chi^{-1}$ at $x$ viewed as a unit and $|x|$ the modulus of $x$, i.e. the scaling factor of multiplication by $x$ on Haar measure (equal to $\|x\|$ by [`LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm`](thm.html#LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm)), both extended by $0$ at $x=0$.
--
--   This is the standard local computation, in the style of Tate's local theory, that the unramified $\mathrm{GL}_2$ intertwining integrand integrates to zero against an additive twist $\psi(-\xi x)$ when $\xi$ lies outside the lattice dual to the level of $\psi$. It feeds the computation of the Whittaker coefficients of Bruhat–Eisenstein series as a character times an Euler product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinGeneral_LocalUnr_integral_twisted_eq_zero_of_exp_lt.lean

import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_LanglandsTunnell_TateLocalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

theorem EisensteinGeneral.LocalUnr.integral_twisted_eq_zero_of_exp_lt
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
    (ξ : v.adicCompletion F) (hξ : WithZero.exp n < Valued.v ξ) :
    ∫ x, (((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator (fun _ => (1 : ℂ)) x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1))) x)
          * ψ (-(ξ * x))) ∂μ
      = 0 := by sorry
