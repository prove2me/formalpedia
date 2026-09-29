-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuous_iwasawa_weyl_unipotent
-- name    : AutomorphicForm.exists_continuous_iwasawa_weyl_unipotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/b9b6a8d2-aa1f-5655-937a-03ba540103b3
-- title:
--   Continuous Iwasawa decomposition of w⁻¹n(x) over the adeles
-- statement:
--   Let $F$ be a number field, with adele ring $\mathbb{A}=\mathbb{A}_F$, and let $\alpha\colon\mathbb{A}^\times\to\mathbb{R}^\times$ be the character on units obtained from the distributive (module) Haar character `distribHaarChar` of $\mathbb{A}$ by pushing its values from $\mathbb{R}_{\ge 0}$ into $\mathbb{R}$. Assume $h\alpha$: $\alpha(t)>0$ for every $t$. Then there is a map $\kappa\colon\mathbb{A}\to\mathrm{GL}_2(\mathbb{A})$ such that: $\kappa$ is continuous; for every $x$ the finite part `glFin` of $\kappa(x)$ lies in the level-$\top$ integral subgroup `finiteIntegralGL2`, and for each infinite place $w$ the $w$-component of the archimedean part `glArch` of $\kappa(x)$ satisfies `IsRowIsometry`, i.e. its determinant has norm $1$ and $(x,y)\mapsto(x,y)k$ preserves $\|\cdot\|^2+\|\cdot\|^2$; for every $x$ the element $w^{-1}n(x)\kappa(x)^{-1}$ lies in `adelicBorel`, the subgroup of matrices with vanishing $(1,0)$ entry, where $w$ is `adelicWeyl`, the image of the Weyl element of $\mathrm{GL}_2(F)$, and $n(x)$ is $\begin{pmatrix}1&x\\0&1\end{pmatrix}$; $\kappa$ is local in each coordinate, in that the $v$-component of the finite part of $\kappa(x)$ depends only on the $v$-component of $x$ for each finite place $v$, and the archimedean part of $\kappa(x)$ depends only on the archimedean part of $x$; and finally, for every $s\in\mathbb{C}$ and every $\varphi\colon\mathrm{GL}_2(\mathbb{A})\to\mathbb{C}$ with $\varphi(bg)=\eta_1(b_1)\eta_2(b_2)\varphi(g)$ for all Borel elements $b$ with diagonal entries $b_1,b_2$, where $\eta_1=\alpha^{s+1/2}$ and $\eta_2=\alpha^{-(s+1/2)}$ (the characters `etaFst 1 α hα s`, `etaSnd 1 α hα s`), one has $\varphi(w^{-1}n(x))=H(w^{-1}n(x))^{s+1/2}\,\varphi(\kappa(x))$ for all $x\in\mathbb{A}$, with $H$ the adelic height `adelicHeight`, the product of its archimedean and finite heights.
--
--   This is the Iwasawa decomposition of the big-cell representatives $w^{-1}n(x)$ in $\mathrm{GL}_2(\mathbb{A})$, in the form of a continuous, coordinatewise local choice of maximal-compact factor $\kappa(x)$, together with the resulting evaluation of an induced section at $w^{-1}n(x)$ in terms of the adelic height. It supplies the change of variables used in the analysis of the Weyl intertwining integral, in particular in the estimate [`AutomorphicForm.exists_pos_eventually_le_re_sub_one_half_mul_weylIntertwiningIntegral_one_of_nonneg_of_isArchKFinite_family`](thm.html#AutomorphicForm.exists_pos_eventually_le_re_sub_one_half_mul_weylIntertwiningIntegral_one_of_nonneg_of_isArchKFinite_family).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuous_iwasawa_weyl_unipotent.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicLevel
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHeight IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal

theorem AutomorphicForm.exists_continuous_iwasawa_weyl_unipotent
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)),
    ∃ κ : AdeleRing (𝓞 F) F → AdelicGL2 (𝓞 F) F,
      Continuous κ ∧
      (∀ x, glFin (𝓞 F) F (κ x) ∈ finiteIntegralGL2 (𝓞 F) F ∧
        ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F (κ x)))) ∧
      (∀ x, (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * (κ x)⁻¹ ∈ adelicBorel (𝓞 F) F) ∧
      (∀ x y : AdeleRing (𝓞 F) F, ∀ v : HeightOneSpectrum (𝓞 F), x.2 v = y.2 v →
        finComponent (𝓞 F) F v (glFin (𝓞 F) F (κ x)) = finComponent (𝓞 F) F v (glFin (𝓞 F) F (κ y))) ∧
      (∀ x y : AdeleRing (𝓞 F) F, x.1 = y.1 → glArch (𝓞 F) F (κ x) = glArch (𝓞 F) F (κ y)) ∧
      (∀ (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ),
        IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ →
        ∀ x : AdeleRing (𝓞 F) F,
          φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) =
            ((adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) : ℝ) : ℂ) ^ (s + 1 / 2) * φ (κ x)) := by sorry
