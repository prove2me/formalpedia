-- Prove2me | Theorems.Thm_AutomorphicForm_setIntegral_fundamentalDomain_slab_eq_measureReal_smul_integral_of_forall_integral_eq_one
-- name    : AutomorphicForm.setIntegral_fundamentalDomain_slab_eq_measureReal_smul_integral_of_forall_integral_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/625ad819-6249-57cd-8d00-894c50fe6e8d
-- title:
--   Torus quotient in a determinant slab for GL₂(A_F)
-- statement:
--   Let $F$ be a number field and let $G = \mathrm{GL}_2(\mathbb{A}_F)$ be the group of invertible $2\times 2$ matrices over the adele ring of $F$, carrying the Borel structure attached to its topology; write $\|\det g\|$ for the real number obtained by evaluating the distributive Haar character of $\mathbb{A}_F$ at the idele $\det g$. Let $\mu$ be an s-finite left-invariant measure on $G$, let $T \le G$ be a subgroup with its Borel structure and $\tau$ an s-finite right-invariant measure on $T$, and assume that for every real $c>0$ there is an element $t$ of the centre of $T$ with $\|\det t\| = c$. Let $\Gamma \le \mathrm{GL}_2(F)$ be a subgroup whose image $\iota(\Gamma)$ under the map $\iota$ induced on $\mathrm{GL}_2$ by the structure map $F \to \mathbb{A}_F$ is contained in $T$. Fix reals $\alpha > 0$ and $\beta$, and let $S = \{g \in G : \|\det g\| \in [\alpha,\beta]\}$. Assume $\Psi \subseteq G$ is a fundamental domain for the left translation action of $\iota(\Gamma)$ with respect to $\mu|_S$, and $D \subseteq T$ is a fundamental domain with respect to $\tau$ for the action of $\iota(\Gamma) \cap T$, viewed inside $T$, through the opposite group, i.e. by right translation. Let $E$ be a real normed space, $h \colon G \to E$ strongly measurable with $h(tx) = h(x)$ for all $t \in T$ and $x \in G$, and $W \colon G \to \mathbb{R}$ measurable and nonnegative with $\int_T W(tx)\,d\tau(t) = 1$ for every $x$ at which $h(x) \neq 0$. Then $$\int_{\Psi} h \, d(\mu|_S) = \tau\bigl(D \cap \{t \in T : \|\det t\| \in [\alpha,\beta]\}\bigr) \cdot \int_G W(x)\, h(x)\, d\mu(x),$$ the measure of the slab in $D$ being taken as a real number.
--
--   This is the torus-quotient step on the geometric side of the trace formula for $\mathrm{GL}_2$ over a number field: integration of a $T$-invariant function over a fundamental domain in a determinant slab is converted into the volume of the corresponding slab in $\Gamma\backslash T$ times an integral over $G$ weighted by a section function $W$ for $T$. It is used by the statements identifying such slab integrals with multiples of orbital integrals and of integrals over the centraliser of a global element.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_setIntegral_fundamentalDomain_slab_eq_measureReal_smul_integral_of_forall_integral_eq_one.lean

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.setIntegral_fundamentalDomain_slab_eq_measureReal_smul_integral_of_forall_integral_eq_one
    (F : Type) [Field F] [NumberField F]
    (μ : Measure (AutomorphicForm.AdelicGL2 (𝓞 F) F)) [SFinite μ] [μ.IsMulLeftInvariant]
    (T : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 F) F)) [MeasurableSpace T] [BorelSpace T]
    (τ : Measure T) [SFinite τ] [τ.IsMulRightInvariant]
    (hT : ∀ c : ℝ, 0 < c → ∃ t : T, t ∈ Subgroup.center T ∧
      NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det (t : AutomorphicForm.AdelicGL2 (𝓞 F) F)) = c)
    (Γ : Subgroup (GL (Fin 2) F)) (hΓ : Γ.map (AutomorphicForm.globalPoints (𝓞 F) F) ≤ T)
    (α β : ℝ) (hα : 0 < α)
    (Ψ : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F))
    (hΨ : IsFundamentalDomain (Γ.map (AutomorphicForm.globalPoints (𝓞 F) F)) Ψ
      (μ.restrict {g | NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈
        Set.Icc α β}))
    (D : Set T)
    (hD : IsFundamentalDomain
      ((Γ.map (AutomorphicForm.globalPoints (𝓞 F) F)).subgroupOf T).op D τ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : AutomorphicForm.AdelicGL2 (𝓞 F) F → E) (hhm : StronglyMeasurable h)
    (hhT : ∀ t ∈ T, ∀ x, h (t * x) = h x)
    (W : AutomorphicForm.AdelicGL2 (𝓞 F) F → ℝ) (hW0 : ∀ x, 0 ≤ W x) (hWm : Measurable W)
    (hW : ∀ x, h x ≠ 0 → ∫ t : T, W ((t : AutomorphicForm.AdelicGL2 (𝓞 F) F) * x) ∂τ = 1) :
    ∫ x in Ψ, h x ∂(μ.restrict {g | NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) =
      (τ.real (D ∩ {t | NumberField.TateGlobal.ideleNorm F
        (Matrix.GeneralLinearGroup.det (t : AutomorphicForm.AdelicGL2 (𝓞 F) F)) ∈ Set.Icc α β})) •
        ∫ x, W x • h x ∂μ := by sorry
