-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_forall_setIntegral_sub_constantTerm_mul_eq_zero_canonicalTruncationDomain_inter_lt_adelicHeight
-- name    : AutomorphicForm.exists_pos_forall_setIntegral_sub_constantTerm_mul_eq_zero_canonicalTruncationDomain_inter_lt_adelicHeight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/3e09134a-f81a-570b-85b3-ca5d13c4d385
-- title:
--   Vanishing of the constant-term defect pairing on the cusp region
-- statement:
--   Let $K$ be a number field and let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$. Then there exists $T_0>0$ such that for every $T\ge T_0$ the following holds. Let $a,d:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be measurable functions on [`AutomorphicForm.AdelicGL2 (𝓞 K) K`](def/AutomorphicForm_AdelicLsXi.html#L12), the general linear group of degree $2$ over the adele ring of $K$, for the Borel $\sigma$-algebra, such that both $a$ and $d$ are invariant under left translation by the image under [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15) (the map induced by $K\to\mathbb{A}_K$) of every $\gamma\in\mathrm{GL}_2(K)$ whose $(1,0)$ entry vanishes, and such that $d$ is moreover invariant under left translation by $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ for every $x\in\mathbb{A}_K$. Write $a_N(g)=\int a\bigl(\begin{pmatrix}1&x\\0&1\end{pmatrix}g\bigr)\,dx$, the integral being over the additive Haar measure of $\mathbb{A}_K$ conditioned on the adelic box $\{x:x_\infty\in\text{infiniteBox}(K),\ x_{\mathrm{fin}}\ \text{integral at every finite place}\}$. If $g\mapsto (a(g)-a_N(g))\,d(g)$ is integrable, for the Haar measure `adelicGLHaar` of $\mathrm{GL}_2(\mathbb{A}_K)$, on the intersection of the canonical truncation domain `canonicalTruncationDomain K α β` (the set component of a classically chosen truncation datum for $\alpha,\beta$, empty if none exists) with $\{g:T<\mathrm{adelicHeight}_K(g)\}$, then its integral over that intersection is $0$.
--
--   This is the analytic core, for $\mathrm{GL}_2$ over a number field in the determinant-slab normalisation, of the assertion that Arthur's truncation operator is an orthogonal projection: above height $T$ the constant-term defect $a-a_N$ pairs to zero against any function invariant under the rational Borel subgroup and under the full adelic unipotent group. It is used in the proof that the pairing of $\Lambda^T\varphi$ with $\psi$ over the canonical truncation domain equals the pairing of $\Lambda^T\varphi$ with $\Lambda^T\psi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_forall_setIntegral_sub_constantTerm_mul_eq_zero_canonicalTruncationDomain_inter_lt_adelicHeight.lean

import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.adeleBorel

theorem AutomorphicForm.exists_pos_forall_setIntegral_sub_constantTerm_mul_eq_zero_canonicalTruncationDomain_inter_lt_adelicHeight
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ (a d : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ), Measurable a → Measurable d →
        (∀ γ ∈ AutomorphicForm.borelSubgroup K, ∀ g : AutomorphicForm.AdelicGL2 (𝓞 K) K,
          a (AutomorphicForm.globalPoints (𝓞 K) K γ * g) = a g) →
        (∀ γ ∈ AutomorphicForm.borelSubgroup K, ∀ g : AutomorphicForm.AdelicGL2 (𝓞 K) K,
          d (AutomorphicForm.globalPoints (𝓞 K) K γ * g) = d g) →
        (∀ (x : AdeleRing (𝓞 K) K) (g : AutomorphicForm.AdelicGL2 (𝓞 K) K),
          d (AutomorphicForm.unipotentGL2 x * g) = d g) →
        IntegrableOn
          (fun g => (a g - AutomorphicForm.constantTerm
              (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
              (fun x => AutomorphicForm.unipotentGL2 x) a g) * d g)
          (AutomorphicForm.canonicalTruncationDomain K α β ∩ {g | T < NumberField.AdelicHeight.adelicHeight K g})
          (adelicGLHaar (Fin 2) (𝓞 K) K) →
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β ∩ {g | T < NumberField.AdelicHeight.adelicHeight K g},
            (a g - AutomorphicForm.constantTerm
                (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K))
                (fun x => AutomorphicForm.unipotentGL2 x) a g) * d g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by sorry
