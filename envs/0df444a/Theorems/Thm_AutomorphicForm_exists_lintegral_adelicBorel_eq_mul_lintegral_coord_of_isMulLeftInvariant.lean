-- Prove2me | Theorems.Thm_AutomorphicForm_exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant
-- name    : AutomorphicForm.exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/1807034d-0ee0-54ce-8420-520499d1beaf
-- title:
--   Left Haar measure of the adelic Borel subgroup in coordinates
-- statement:
--   Let $K$ be a number field, $\mathbb{A}=\mathbb{A}_K$ its adele ring, and let $B \le \mathrm{GL}_2(\mathbb{A})$ be the subgroup `adelicBorel` of those invertible $2\times 2$ adelic matrices whose $(1,0)$ entry vanishes, with $\mathrm{GL}_2(\mathbb{A})$, $\mathbb{A}$ and $\mathbb{A}^\times$ carrying their Borel $\sigma$-algebras. Let $\mu_B$ be a measure on $B$ that is invariant under left translation, finite on compact sets and positive on non-empty open sets. The assertion is that there exists $c \in [0,\infty]$ with $c \neq 0$ and $c \neq \infty$ such that for every measurable $F \colon \mathrm{GL}_2(\mathbb{A}) \to [0,\infty]$ one has $$\int_{B} F(b)\,d\mu_B(b) = c \int_{\mathbb{A}} \int_{\mathbb{A}^\times} \int_{\mathbb{A}^\times} F\bigl(n(x)\,z(u)\,a(t)\bigr)\,\|t\|^{-1}\,d^{\times}t\,d^{\times}u\,dx,$$ as an identity of lower Lebesgue integrals, where $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ is `unipotentGL2`, $z(u)$ is the scalar matrix $u \cdot 1$ given by `centralScalar`, $a(t)$ is the diagonal matrix with entries $t, 1$ given by `diagOne`, $dx$ is the additive Haar measure `adelicAddHaar` on $\mathbb{A}$, $d^{\times}$ is the Haar measure `idelicHaar` on $\mathbb{A}^\times$, and $\|t\|$ is [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), the value at $t$ of the distributive Haar character of $\mathbb{A}$, the factor being inserted as $\mathrm{ofReal}(\|t\|^{-1})$. The innermost integration is in $t$, the outermost in $x$.
--
--   This is the computation of a left Haar measure on the adelic Borel subgroup of $\mathrm{GL}_2$ — an $ax+b$-type group — in the coordinates unipotent times centre times torus, the modulus factor $\|t\|^{-1}$ accounting for the non-unimodularity. It is used to obtain the corresponding integration formula for Haar measure on $\mathrm{GL}_2(\mathbb{A})$ in the Iwasawa coordinates, in [`NumberField.AdelicHaar.exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa`](thm.html#NumberField.AdelicHaar.exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant.lean

import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_NumberField_IdeleProductMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem AutomorphicForm.exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant
    (K : Type) [Field K] [NumberField K]
    (μB : Measure (adelicBorel (𝓞 K) K)) [μB.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μB]
    [μB.IsOpenPosMeasure] :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∀ F : AdelicGL2 (𝓞 K) K → ℝ≥0∞, Measurable F →
        ∫⁻ b, F (b : AdelicGL2 (𝓞 K) K) ∂μB =
          c * ∫⁻ x, ∫⁻ u, ∫⁻ t,
                F (unipotentGL2 x * centralScalar (𝓞 K) K u * diagOne t) *
                  ENNReal.ofReal ((NumberField.TateGlobal.ideleNorm K t)⁻¹)
              ∂(NumberField.Idele.idelicHaar K) ∂(NumberField.Idele.idelicHaar K) ∂(adelicAddHaar (𝓞 K) K) := by sorry
