-- Prove2me | Theorems.Thm_AutomorphicForm_integral_mul_conj_unipotent_eq_tsum_units_whittakerCoefficient_one_diagOne_and_tsum_norm_le
-- name    : AutomorphicForm.integral_mul_conj_unipotent_eq_tsum_units_whittakerCoefficient_one_diagOne_and_tsum_norm_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/f7f15b34-343c-59b4-a83d-b38fafd7c670
-- title:
--   Parseval step of Rankin–Selberg unfolding over the rational torus
-- statement:
--   Let $F$ be a number field, let $D$ be a subset of $\mathrm{GL}_2(\mathbb{A}_F)$, let $U$ assign to each ideal of $\mathcal{O}_F$ a subgroup of $\mathrm{GL}_2(\mathbb{A}_F)$ and let $\mathrm{gen}$ assign an element of $\mathrm{GL}_2(\mathbb{A}_F)$ to each height-one prime of $\mathcal{O}_F$; these data are assembled, together with the adelic box (infinite part a fundamental domain for the Minkowski lattice, finite part the integral finite adeles), into the pins `productionPinsOf F D U gen (adelicBox F)`, whose measure $\nu$ on $\mathbb{A}_F$ is the adelic additive Haar measure conditioned on that box. Let $\psi$ be an additive character of $\mathbb{A}_F$ which is continuous, nontrivial and trivial on the image of $F$, and write $W_\alpha\varphi(g)=\int \varphi(n(u)g)\,\psi(-\alpha u)\,d\nu(u)$ for the Whittaker coefficient at $\alpha \in F$, where $n(u)$ is the upper unipotent matrix with entry $u$. Let $x,y:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be continuous and invariant under left multiplication by the image of $\mathrm{GL}_2(F)$, assume $W_0x(g)=0$ for all $g$ and that $\alpha\mapsto\|W_\alpha x(g)\|$ is summable over $F$ for every $g$, and fix $g\in \mathrm{GL}_2(\mathbb{A}_F)$. Writing $\delta_a$ for the image in $\mathrm{GL}_2(\mathbb{A}_F)$ of $\mathrm{diag}(a,1)\in\mathrm{GL}_2(F)$, the conclusion is threefold: the family $a\mapsto \|W_1x(\delta_a g)\|\,\|W_1y(\delta_a g)\|$ is summable over $a\in F^\times$; its sum is at most $\bigl(\int\|x(n(u)g)\|^2 d\nu\bigr)^{1/2}\bigl(\int\|y(n(u)g)\|^2 d\nu\bigr)^{1/2}$; and $\int x(n(u)g)\overline{y(n(u)g)}\,d\nu(u)=\sum_{a\in F^\times} W_1x(\delta_a g)\overline{W_1y(\delta_a g)}$. No summability of the Whittaker coefficients of $y$ is assumed.
--
--   This is the Parseval/Plancherel step of the Rankin–Selberg unfolding on $\mathrm{GL}_2$ along the compact quotient $N(F)\backslash N(\mathbb{A}_F)\cong F\backslash\mathbb{A}_F$, with the Fourier expansion rewritten over the rational torus via $W_\alpha\varphi(g)=W_1\varphi(\mathrm{diag}(\alpha,1)g)$ for $\alpha\neq 0$ and the $\alpha=0$ term removed by the cuspidality hypothesis on $x$, together with the Cauchy–Schwarz bound coming from Bessel's inequality. It feeds the computations of Petersson-type integrals against Bruhat–Eisenstein data over the rational centre–unipotent quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_mul_conj_unipotent_eq_tsum_units_whittakerCoefficient_one_diagOne_and_tsum_norm_le.lean

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.integral_mul_conj_unipotent_eq_tsum_units_whittakerCoefficient_one_diagOne_and_tsum_norm_le
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (x y : AdelicGL2 (𝓞 F) F → ℂ)
    (hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      x (globalPoints (𝓞 F) F γ * g) = x g)
    (hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      y (globalPoints (𝓞 F) F γ * g) = y g)
    (hxc : Continuous x) (hyc : Continuous y)
    (hx0 : ∀ g, whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 0 g = 0)
    (hxW : ∀ g, Summable fun a : F =>
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x a g‖)
    (g : AdelicGL2 (𝓞 F) F) :
    (Summable fun a : Fˣ =>
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1
          (globalPoints (𝓞 F) F (diagOne a) * g)‖ *
        ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1
          (globalPoints (𝓞 F) F (diagOne a) * g)‖) ∧
    (∑' a : Fˣ,
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1
          (globalPoints (𝓞 F) F (diagOne a) * g)‖ *
        ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1
          (globalPoints (𝓞 F) F (diagOne a) * g)‖) ≤
      Real.sqrt (∫ u, ‖x (unipotentGL2 u * g)‖ ^ 2 ∂(productionPinsOf F D U gen (adelicBox F)).ν) *
        Real.sqrt (∫ u, ‖y (unipotentGL2 u * g)‖ ^ 2 ∂(productionPinsOf F D U gen (adelicBox F)).ν) ∧
    ∫ u, x (unipotentGL2 u * g) * (starRingEnd ℂ) (y (unipotentGL2 u * g))
        ∂(productionPinsOf F D U gen (adelicBox F)).ν =
      ∑' a : Fˣ,
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ x 1
            (globalPoints (𝓞 F) F (diagOne a) * g) *
          (starRingEnd ℂ) (whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ y 1
            (globalPoints (𝓞 F) F (diagOne a) * g)) := by sorry
