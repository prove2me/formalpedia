-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_forall_setIntegral_lambdaT_mul_conj_eq_setIntegral_lambdaT_mul_conj_lambdaT_canonicalTruncationDomain
-- name    : AutomorphicForm.exists_pos_forall_setIntegral_lambdaT_mul_conj_eq_setIntegral_lambdaT_mul_conj_lambdaT_canonicalTruncationDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/f3dd96f1-4da9-59fd-8545-c813360674dc
-- title:
--   Self-adjointness of truncation on the canonical truncation domain
-- statement:
--   Let $K$ be a number field, and let $\alpha,\beta$ be real numbers with $0<\alpha$ and $\alpha<\beta$. Write $G=\mathrm{GL}_2(\mathbb{A}_K)$ for `AdelicGL2 (𝓞 K) K`, equipped with its Borel $\sigma$-algebra and the Haar measure `adelicGLHaar`, and let $\Phi_0=$ `canonicalTruncationDomain K α β` be the set component selected (via choice) from a datum satisfying `IsTruncationDatum K α β`, and $\emptyset$ if no such datum exists. For $T\in\mathbb{R}$ let $\Lambda^T\varphi(g)=\varphi(g)-\mathbf{1}_{\{H>T\}}(g)\,\varphi_N(g)$ be `lambdaT`, where $H$ is the adelic height (the product of the archimedean and finite heights of the corresponding components of $g$) and $\varphi_N$ is `constantTerm` for the unipotent map $x\mapsto n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$ and for the additive adelic Haar measure conditioned on the box `adelicBox K` (archimedean part in the infinite box, finite part an integral finite adele). The assertion is: there exists $T_0>0$ such that for every $T\ge T_0$ and all measurable $a,b:G\to\mathbb{C}$ which satisfy $a(\gamma g)=a(g)$ and $b(\gamma g)=b(g)$ for all $g$ and all $\gamma$ in the image under `globalPoints` of the subgroup of $\mathrm{GL}_2(K)$ of matrices with vanishing $(1,0)$ entry, if $\Lambda^T a\cdot\overline{b}$ and $\Lambda^T a\cdot\overline{\Lambda^T b}$ are both integrable on $\Phi_0$, then $\int_{\Phi_0}\Lambda^T a\,\overline{b}=\int_{\Phi_0}\Lambda^T a\,\overline{\Lambda^T b}$.
--
--   This is the statement that Arthur's truncation operator acts as an orthogonal projection on the canonical truncation domain of $\mathrm{GL}_2$ over a number field, in the determinant-slab normalisation: combined with its conjugate it gives self-adjointness of $\Lambda^T$ and $\|\Lambda^T\varphi\|^2=\langle\Lambda^T\varphi,\varphi\rangle$. It is used in the derivation of the Maass–Selberg relations for truncated pseudo-Eisenstein series on vertical slabs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_forall_setIntegral_lambdaT_mul_conj_eq_setIntegral_lambdaT_mul_conj_lambdaT_canonicalTruncationDomain.lean

import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

theorem AutomorphicForm.exists_pos_forall_setIntegral_lambdaT_mul_conj_eq_setIntegral_lambdaT_mul_conj_lambdaT_canonicalTruncationDomain
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ (a b : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ), Measurable a → Measurable b →
        (∀ γ ∈ AutomorphicForm.borelSubgroup K, ∀ g : AutomorphicForm.AdelicGL2 (𝓞 K) K,
          a (AutomorphicForm.globalPoints (𝓞 K) K γ * g) = a g) →
        (∀ γ ∈ AutomorphicForm.borelSubgroup K, ∀ g : AutomorphicForm.AdelicGL2 (𝓞 K) K,
          b (AutomorphicForm.globalPoints (𝓞 K) K γ * g) = b g) →
        IntegrableOn
          (fun g => AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight K) T a g *
            conj (b g))
          (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) →
        IntegrableOn
          (fun g => AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight K) T a g *
            conj (AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight K) T b g))
          (AutomorphicForm.canonicalTruncationDomain K α β) (adelicGLHaar (Fin 2) (𝓞 K) K) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
            AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight K) T a g *
            conj (b g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
          = ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
            AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight K) T a g *
            conj (AutomorphicForm.lambdaT (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun x => AutomorphicForm.unipotentGL2 x) (NumberField.AdelicHeight.adelicHeight K) T b g)
              ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
