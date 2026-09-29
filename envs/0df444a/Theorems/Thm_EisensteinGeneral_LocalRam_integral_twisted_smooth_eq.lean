-- Prove2me | Theorems.Thm_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq
-- name    : EisensteinGeneral.LocalRam.integral_twisted_smooth_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/6f0e1867-949a-5883-b871-2095c8e12d11
-- title:
--   Shell expansion of a twisted local smooth integral
-- statement:
--   Let $F$ be a number field, $v$ a height-one prime of $\mathcal O_F$, $F_v$ the $v$-adic completion with valuation $\mathrm{v}$ (normalised so that $\mathrm{v}(x)\le \exp(k)$ means $x$ lies in the $k$-th fractional power of the maximal ideal in the reverse direction), $\mathcal O_v$ its ring of integers, and $q_v=$ `Ideal.absNorm v.asIdeal`; let $\mu$ be an additive Haar measure on $F_v$ for a Borel measurable structure. Assume given a unit $\varpi$ of $F_v$ with $\mathrm{v}(\varpi)=\exp(-1)$, a homomorphism $\chi\colon F_v^\times\to\mathbb C^\times$, an integer $c\ge 1$ such that $\chi(u)=1$ for every unit $u$ with $\mathrm{v}(u)=1$ and $\mathrm{v}(u-1)\le\exp(-c)$, an integer $m\ge 1$, a function $A\colon F_v\to\mathbb C$ integrable on $\mathcal O_v$, a function $B\colon F_v\to\mathbb C$ with $B(y)=B(x)$ whenever $\mathrm{v}(y-x)\le\exp(-m)$, and $s\in\mathbb C$ with $\bigl\|\chi(\varpi)\,q_v^{-2s}\bigr\|<1$. Assume further an additive character $\psi\colon F_v\to\mathbb C$ and $n\in\mathbb Z$ with $\psi(x)=1$ whenever $\mathrm{v}(x)\le\exp(n)$ and $\psi(x)\ne 1$ for some $x$ with $\mathrm{v}(x)\le\exp(n+1)$, and $\xi\in F_v$, $e\in\mathbb Z$ with $\mathrm{v}(\xi)=\exp(e)$. Then the integral over $F_v$ of $$\bigl(\mathbf 1_{\mathcal O_v}(x)A(x)+\mathbf 1_{F_v\setminus\mathcal O_v}(x)\,\chi^{-1}(x)\,|x|_v^{-(2s+1)}B(x^{-1})\bigr)\,\psi(-\xi x)$$ against $\mu$ equals $\int_{\mathcal O_v}A(x)\psi(-\xi x)\,d\mu$ plus $\sum_{k=1}^{K}\bigl(q_v^{-(2s+1)}\bigr)^{k}\int_{\mathrm{v}(x)=\exp(k)}\chi^{-1}(x)B(x^{-1})\psi(-\xi x)\,d\mu$, where $K$ is the natural-number truncation of $\max(m-1,\;n+c-e)$. Here $\chi^{-1}(x)$ denotes `charExt` of $\chi^{-1}$, that is $\chi^{-1}$ on $F_v^\times$ and $0$ at $x=0$, and $|x|_v$ denotes `modulus`, the scaling factor of multiplication by $x$ on Haar measure (equal to $0$ at $x=0$).
--
--   This is the twisted (against an additive character $\psi(-\xi\,\cdot)$) form of the shell decomposition of a local integral of a smooth section, the finite-place analogue of the Tate-style local computation: the part of the integrand outside $\mathcal O_v$ is resolved into finitely many valuation shells, the tail beyond $K=\max(m-1,n+c-e)$ contributing nothing. It is used, together with the untwisted shell expansion [`AutomorphicForm.LocalIntertwining.integral_smoothWeylIntegrand_adicCompletion`](thm.html#AutomorphicForm.LocalIntertwining.integral_smoothWeylIntegrand_adicCompletion) and the identification of `modulus` with the normalised absolute value on $F_v$, in the evaluation of Whittaker coefficients of Bruhat–Eisenstein series as an Euler product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.lean

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField

theorem EisensteinGeneral.LocalRam.integral_twisted_smooth_eq
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
    (hψn' : ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (ξ : v.adicCompletion F) (e : ℤ) (hξ : Valued.v ξ = WithZero.exp e) :
    ∫ x, (((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x)
          * ψ (-(ξ * x))) ∂μ
      = (∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), A x * ψ (-(ξ * x)) ∂μ)
        + ∑ k ∈ Finset.Icc 1 (max ((m : ℤ) - 1) (n + (c : ℤ) - e)).toNat,
            (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ k
              * ∫ x in {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)},
                  LanglandsTunnell.TateLocal.charExt χ⁻¹ x * B x⁻¹ * ψ (-(ξ * x)) ∂μ := by sorry
