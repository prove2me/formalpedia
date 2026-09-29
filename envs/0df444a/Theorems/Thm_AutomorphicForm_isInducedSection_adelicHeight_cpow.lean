-- Prove2me | Theorems.Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow
-- name    : AutomorphicForm.isInducedSection_adelicHeight_cpow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/a8119824-be5c-5819-b173-a5a0eb4cfef5
-- title:
--   Adelic height powers form a Borel-induced flat section
-- statement:
--   Let $F$ be a number field (a field with the `NumberField` structure), with adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F` and idele group $\mathbb{A}_F^\times$. Write $\alpha : \mathbb{A}_F^\times \to \mathbb{R}^\times$ for the monoid homomorphism obtained from the module Haar character `distribHaarChar (AdeleRing (𝓞 F) F)`, which records the factor by which scaling by an idele dilates additive Haar measure on $\mathbb{A}_F$, by pushing its $\mathbb{R}_{\ge 0}$-values into $\mathbb{R}$ and passing to units. The theorem asserts three things simultaneously. First, $\alpha(x) > 0$ as a real number for every idele $x$. Second, the trivial homomorphism $1 : \mathbb{A}_F^\times \to \mathbb{C}^\times$ satisfies $\|1\| = 1$ at every idele, i.e. it is unitary in the sense of `IsUnitaryChar`. Third, for every proof $h_\alpha$ of that positivity and every $s \in \mathbb{C}$, the function $\varphi(g) = (\mathrm{adelicHeight}_F(g))^{s+1/2}$ (complex power of the real adelic height, the product over infinite places of the local heights of the archimedean components raised to the place multiplicities, times the finite product over the nonzero primes of $\mathcal{O}_F$ of the local heights of the finite components) satisfies the induction law for the characters $\chi_1 = \mathbf{1}\cdot\alpha^{\,s+1/2}$ and $\chi_2 = \mathbf{1}\cdot\alpha^{-(s+1/2)}$, namely $\varphi(bg) = \chi_1(b_{00})\,\chi_2(b_{11})\,\varphi(g)$ for every $g \in \mathrm{GL}_2(\mathbb{A}_F)$ and every $b$ in the adelic Borel subgroup, the elements of $\mathrm{GL}_2(\mathbb{A}_F)$ whose lower-left entry vanishes, $b_{00}$ and $b_{11}$ being its diagonal entries viewed as ideles.
--
--   This is the statement that the adelic height furnishes the flat (spherical) section of the degenerate principal series of $\mathrm{GL}_2(\mathbb{A}_F)$ induced from the character $(\delta^{s+1/2}, \delta^{-(s+1/2)})$ of the Borel subgroup, in the normalisation whose unitary axis is $\operatorname{Re} s = 0$. It is the starting point for the construction of the associated Eisenstein series and is invoked throughout the analysis of the Weyl intertwining integral and of the big-cell expansions of the corresponding family of sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isInducedSection_adelicHeight_cpow.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_NumberField_AdelicHeight

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory NumberField NumberField.AdelicHeight AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.isInducedSection_adelicHeight_cpow
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    (∀ x, 0 < ((α x : ℝˣ) : ℝ)) ∧
    IsUnitaryChar (𝓞 F) F (1 : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) ∧
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (s : ℂ),
      IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s)
        (fun g : AdelicGL2 (𝓞 F) F => ((adelicHeight F g : ℝ) : ℂ) ^ (s + 1 / 2)) := by sorry
