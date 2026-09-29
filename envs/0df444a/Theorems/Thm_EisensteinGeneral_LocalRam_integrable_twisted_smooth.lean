-- Prove2me | Theorems.Thm_EisensteinGeneral_LocalRam_integrable_twisted_smooth
-- name    : EisensteinGeneral.LocalRam.integrable_twisted_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/fc6038eb-b685-52cd-bdde-08e07ca66d4d
-- title:
--   Integrability of the twisted smooth local integrand at a finite place
-- statement:
--   Let $F$ be a number field, $v$ a nonzero prime of $\mathcal O_F$, and $F_v$ the $v$-adic completion, equipped with its Borel $\sigma$-algebra and an additive Haar measure $\mu$. Let $\varpi \in F_v^{\times}$ satisfy $\mathrm{v}(\varpi)=\mathrm{ofAdd}(-1)$, let $\chi\colon F_v^{\times}\to\mathbb C^{\times}$ be a group homomorphism, and let $c\ge 1$ be such that $\chi(u)=1$ for every unit $u$ with $\mathrm{v}(u)=1$ and $\mathrm{v}(u-1)\le \exp(-c)$. Let $m\ge 1$, let $A\colon F_v\to\mathbb C$ be integrable on $\mathcal O_v$ for $\mu$, and let $B\colon F_v\to\mathbb C$ satisfy $B(y)=B(x)$ whenever $\mathrm{v}(y-x)\le\mathrm{ofAdd}(-m)$. Let $s\in\mathbb C$ satisfy $\bigl\|\chi(\varpi)\,N(v)^{-2s}\bigr\|<1$, where $N(v)$ is the absolute norm of $v$. Let $\psi$ be an additive character of $F_v$ with values in $\mathbb C$ and $n\in\mathbb Z$ with $\psi(x)=1$ whenever $\mathrm{v}(x)\le\exp(n)$, and let $\xi\in F_v$. Then the function $$x\mapsto \Bigl(\mathbf 1_{\mathcal O_v}(x)A(x)+\mathbf 1_{F_v\setminus\mathcal O_v}(x)\,\chi^{-1}(x)\,\bigl(\mathrm{modulus}(x)\bigr)^{-(2s+1)}B(x^{-1})\Bigr)\,\psi(-\xi x)$$ is $\mu$-integrable, where $\chi^{-1}$ is extended by $0$ at $0$ and $\mathrm{modulus}(x)$ is the Haar modulus of multiplication by $x$, set to $0$ at $x=0$.
--
--   This is the integrability statement for the twisted integrand attached to a smooth section at a finite place: the sum of an integrable piece on $\mathcal O_v$ and a tail on $F_v\setminus\mathcal O_v$ built from $\chi^{-1}$, the local modulus to the power $-(2s+1)$ and a locally constant function of $x^{-1}$, multiplied by the additive character $x\mapsto\psi(-\xi x)$. It underlies the local intertwining computations, being used in the results on Weyl-shift and smooth-atom integrals over $F_v$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinGeneral_LocalRam_integrable_twisted_smooth.lean

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField

theorem EisensteinGeneral.LocalRam.integrable_twisted_smooth
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (c : ℕ) (hc : 1 ≤ c) (hχ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v c, χ u = 1)
    (m : ℕ) (hm : 1 ≤ m)
    (A : v.adicCompletion F → ℂ)
    (hA : IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1)
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (ξ : v.adicCompletion F) :
    Integrable (fun x => (((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x)
          * ψ (-(ξ * x)))) μ := by sorry
