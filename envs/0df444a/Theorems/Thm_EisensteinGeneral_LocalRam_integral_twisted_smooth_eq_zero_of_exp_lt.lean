-- Prove2me | Theorems.Thm_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq_zero_of_exp_lt
-- name    : EisensteinGeneral.LocalRam.integral_twisted_smooth_eq_zero_of_exp_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/addfbaf9-6af6-547c-88be-f2270e56d1a4
-- title:
--   Vanishing of a twisted local integral at large frequency
-- statement:
--   Let $F$ be a number field and $v$ a nonzero prime of its ring of integers, with completion $F_v =$ `v.adicCompletion F` carrying its valuation $\mathrm{v}$ with values in $\mathbb{Z}_{m0}$, equipped with a Borel measurable structure and an additive Haar measure $\mu$. Let $\varpi \in F_v^\times$ satisfy $\mathrm{v}(\varpi) = \mathrm{ofAdd}(-1)$, let $\chi \colon F_v^\times \to \mathbb{C}^\times$ be a group homomorphism, and let $c \ge 1$ be such that $\chi(u) = 1$ for every unit $u$ with $\mathrm{v}(u) = 1$ and $\mathrm{v}(u-1) \le \exp(-c)$. Let $m \ge 1$, let $A \colon F_v \to \mathbb{C}$ be integrable on the valuation ring $\mathcal{O}_v$, and let $A$ and $B \colon F_v \to \mathbb{C}$ both be constant on cosets of $\{x : \mathrm{v}(x) \le \mathrm{ofAdd}(-m)\}$, i.e. $\mathrm{v}(y-x) \le \mathrm{ofAdd}(-m)$ implies $A(y)=A(x)$ and $B(y)=B(x)$. Let $s \in \mathbb{C}$ satisfy $\lVert \chi(\varpi)\, N(v)^{-2s} \rVert < 1$, where $N(v)$ is the absolute norm of the ideal $v$. Let $\psi$ be an additive character of $F_v$ with values in $\mathbb{C}$, and $n \in \mathbb{Z}$ such that $\psi$ is trivial on $\{x : \mathrm{v}(x) \le \exp n\}$ while some $x$ with $\mathrm{v}(x) \le \exp(n+1)$ has $\psi(x) \ne 1$. Finally let $\xi \in F_v$ satisfy $\mathrm{v}(\xi) > \exp(n + \max(m,c))$. Then the Bochner integral over $F_v$ against $\mu$ of $$\bigl(\mathbf{1}_{\mathcal{O}_v}(x) A(x) + \mathbf{1}_{F_v \setminus \mathcal{O}_v}(x)\, \chi^{-1}(x)\, \lvert x \rvert_v^{-(2s+1)} B(x^{-1})\bigr)\,\psi(-\xi x)$$ vanishes; here $\chi^{-1}(x)$ denotes `charExt` of $\chi^{-1}$, namely $\chi(x)^{-1}$ for $x \ne 0$ and $0$ for $x = 0$, and $\lvert x \rvert_v$ denotes `modulus`, the scaling factor of Haar measure under multiplication by $x$ (and $0$ for $x=0$), which equals $\lVert x \rVert$ by `modulus_adicCompletion_eq_nnnorm`. No integrability hypothesis is imposed on the full integrand.
--
--   This is the local computation at a finite, possibly ramified, place showing that the Fourier transform of a Tate-type section built from a smooth piece on $\mathcal{O}_v$ and a $\chi^{-1}\lvert\cdot\rvert^{-(2s+1)}$-twisted piece outside $\mathcal{O}_v$ is supported in a lattice determined by the conductors of $\psi$, $\chi$ and the smoothness level $m$. It is used in the evaluation of Whittaker coefficients of Bruhat–Eisenstein series as a character times an Euler product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq_zero_of_exp_lt.lean

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField

theorem EisensteinGeneral.LocalRam.integral_twisted_smooth_eq_zero_of_exp_lt
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
    (hA' : ∀ x y : v.adicCompletion F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A y = A x)
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (ξ : v.adicCompletion F) (hξ : WithZero.exp (n + (max m c : ℕ)) < Valued.v ξ) :
    ∫ x, (((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x)
          * ψ (-(ξ * x))) ∂μ = 0 := by sorry
