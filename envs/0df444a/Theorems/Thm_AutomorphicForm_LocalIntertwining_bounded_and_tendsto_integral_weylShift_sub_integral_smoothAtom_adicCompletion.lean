-- Prove2me | Theorems.Thm_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_weylShift_sub_integral_smoothAtom_adicCompletion
-- name    : AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_weylShift_sub_integral_smoothAtom_adicCompletion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/b1a71a7c-ab5a-5946-aa0c-c0d99f2b929b
-- title:
--   Boundedness and vanishing limit for the local intertwining atom at σdownarrow 1/2
-- statement:
--   Let $F$ be a number field and $v$ a height-one prime of its ring of integers $\mathcal O_F$, and write $F_v$ for the $v$-adic completion, $\mathcal O_v\subset F_v$ for its valuation ring, and $\mathrm{Val}$ for the multiplicative valuation on $F_v$; $F_v$ carries a measurable space structure which is Borel for its topology, and $\mu$ is an additive Haar measure on $F_v$. Let $m$ be a natural number with $m\ge 1$, and let $A,B:F_v\to\mathbb C$ satisfy: $A(y)=A(x)$ whenever $x,y\in\mathcal O_v$ and $\mathrm{Val}(y-x)\le \mathrm{ofAdd}(-m)$, and $B(y)=B(x)$ whenever $x,y\in F_v$ and $\mathrm{Val}(y-x)\le \mathrm{ofAdd}(-m)$. For $\sigma\in\mathbb R$ set $$a_\sigma(x)=\mathbf 1_{\mathcal O_v}(x)\,A(x)+\mathbf 1_{F_v\setminus\mathcal O_v}(x)\,\lvert x\rvert^{-(2\sigma+1)}B(x^{-1}),$$ where $\lvert x\rvert$ denotes the module of $x$, i.e. the scaling factor of Haar measure under multiplication by $x$ (set to $0$ at $x=0$), viewed as a non-negative real and raised to the complex exponent $-(2\sigma+1)$. The assertion is twofold: there exists a real constant $C$ with $\bigl\lVert\int_{F_v}a_\sigma\,d\mu\bigr\rVert\le C$ for every real $\sigma$ with $1/2<\sigma\le 1$; and, as $\sigma$ tends to $1/2$ from the right, $$\int_{F_v}\lvert x\rvert^{-(2\sigma+1)}a_\sigma(x^{-1})\,d\mu(x)-\int_{F_v}a_\sigma(x)\,d\mu(x)\longrightarrow 0 .$$ The integrals are Bochner integrals, so they are $0$ where the integrand fails to be integrable.
--
--   The function $a_\sigma$ is the finite-place atom occurring as the big-cell value of a smooth local section of a principal series at parameter $\sigma$, and $\lvert x\rvert^{-(2\sigma+1)}a_\sigma(x^{-1})$ is its translate by the Weyl element; the statement says that the local intertwining integral of the atom stays bounded on $(1/2,1]$ and that the Weyl-shifted integral has the same limiting behaviour as $\sigma\downarrow 1/2$. It is used in the two results on the behaviour of the Weyl intertwining integral of a flat family near $\sigma=1/2$, [`AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_localWeyl_sub_nhds_zero_of_flat_family`](thm.html#AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_localWeyl_sub_nhds_zero_of_flat_family) and [`AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_archSupportedAt`](thm.html#AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_archSupportedAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_weylShift_sub_integral_smoothAtom_adicCompletion.lean

import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open scoped NNReal

theorem AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_weylShift_sub_integral_smoothAtom_adicCompletion
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (m : ℕ) (_hm : 1 ≤ m)
    (A B : v.adicCompletion F → ℂ)
    (_hA : ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A y = A x)
    (_hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x) :
    let a : ℝ → v.adicCompletion F → ℂ := fun σ x =>
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => (((LanglandsTunnell.TateLocal.modulus y : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)) * B y⁻¹) x
    (∃ C : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → ‖∫ x, a σ x ∂μ‖ ≤ C) ∧
    Tendsto (fun σ : ℝ =>
        (∫ x, (((LanglandsTunnell.TateLocal.modulus x : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)) * a σ x⁻¹ ∂μ)
          - ∫ x, a σ x ∂μ)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by sorry
