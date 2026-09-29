-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_integrableOn_iff_and_setIntegral_lambdaT_mul_conj_lambdaT_eq_of_isTruncationDatum_of_isTruncationDatum
-- name    : AutomorphicForm.exists_forall_integrableOn_iff_and_setIntegral_lambdaT_mul_conj_lambdaT_eq_of_isTruncationDatum_of_isTruncationDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/ed107c74-5e9a-5e1a-a6ea-3c0c3b7a22d6
-- title:
--   Truncated inner products independent of the truncation datum
-- statement:
--   Let $F$ be a number field, $\alpha,\beta$ real numbers, and let $d,d'$ each consist of a quadruple of real numbers together with two subsets of $\mathrm{GL}_2(\mathbb{A}_F)$ (the adele ring of $F$ being formed from $\mathcal{O}_F$). Assume both $d$ and $d'$ satisfy `IsTruncationDatum F α β`, i.e. for $d$: the first real $d_{1,1}$ is positive, the set $d_{2,1}$ is compact, the set $d_{2,2}$ is contained in the union of the right translates $(\cdot\, y)$, for $y \in d_{2,1}$, of the centre-cut Siegel set with parameters $d_{1}$ (finite part integral, all local heights $\ge d_{1,1}$, window squares bounded by $d_{1,2,1}^2$, archimedean determinant norms in $[d_{1,2,2,1},d_{1,2,2,2}]$), $d_{2,2}$ lies in the slab $\{g : \|\det g\| \in [\alpha,\beta]\}$ for the idele norm, and $d_{2,2}$ is a fundamental domain for the left action of the image of $\mathrm{GL}_2(F)$ under `globalPoints` with respect to the Borel Haar measure `adelicGLHaar` restricted to that slab. Then there is $T_0 \in \mathbb{R}$ such that for all $T \ge T_0$ and all $a,b : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ invariant under left multiplication by every `globalPoints` element, the product $\Lambda^T a \cdot \overline{\Lambda^T b}$ is integrable on $d_{2,2}$ against `adelicGLHaar` if and only if it is integrable on $d'_{2,2}$, and the two integrals over $d_{2,2}$ and $d'_{2,2}$ coincide. Here $\Lambda^T \varphi(g) = \varphi(g) - \mathbf{1}_{\{H_F > T\}}(g)\,\varphi_N(g)$, with $H_F$ the adelic height and $\varphi_N$ the constant term of $\varphi$ along the upper unipotent matrices $x \mapsto \begin{pmatrix}1&x\\0&1\end{pmatrix}$ against the adelic Haar measure conditioned on the adelic box. The threshold $T_0$ depends only on $F,\alpha,\beta,d,d'$, not on $a,b$.
--
--   This is the statement that the truncated inner product of two automorphic functions on the determinant slab is independent of the admissible truncation datum used to realise a fundamental domain, once the truncation parameter exceeds the reduction height of the Siegel covers; it is the measure-theoretic counterpart of the invariance properties of Arthur's truncation operator. It is used in the analysis of the continuation of truncated inner products along the determinant axis, in the Maass–Selberg style decomposition of such integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_integrableOn_iff_and_setIntegral_lambdaT_mul_conj_lambdaT_eq_of_isTruncationDatum_of_isTruncationDatum.lean

import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

theorem AutomorphicForm.exists_forall_integrableOn_iff_and_setIntegral_lambdaT_mul_conj_lambdaT_eq_of_isTruncationDatum_of_isTruncationDatum
    (F : Type) [Field F] [NumberField F] (α β : ℝ)
    (d d' : (ℝ × ℝ × ℝ × ℝ) × Set (AutomorphicForm.AdelicGL2 (𝓞 F) F) × Set (AutomorphicForm.AdelicGL2 (𝓞 F) F))
    (hd : AutomorphicForm.IsTruncationDatum F α β d) (hd' : AutomorphicForm.IsTruncationDatum F α β d') :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∀ (a b : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℂ),
        (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AutomorphicForm.AdelicGL2 (𝓞 F) F),
          a (AutomorphicForm.globalPoints (𝓞 F) F γ * g) = a g) →
        (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AutomorphicForm.AdelicGL2 (𝓞 F) F),
          b (AutomorphicForm.globalPoints (𝓞 F) F γ * g) = b g) →
        (IntegrableOn
            (fun g => AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
                (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight F) T a g *
              conj (AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
                (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight F) T b g))
            d.2.2 (adelicGLHaar (Fin 2) (𝓞 F) F) ↔
          IntegrableOn
            (fun g => AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
                (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight F) T a g *
              conj (AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
                (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight F) T b g))
            d'.2.2 (adelicGLHaar (Fin 2) (𝓞 F) F)) ∧
        ∫ g in d.2.2,
            AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight F) T a g *
            conj (AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight F) T b g)
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
          = ∫ g in d'.2.2,
            AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight F) T a g *
            conj (AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight F) T b g)
            ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by sorry
