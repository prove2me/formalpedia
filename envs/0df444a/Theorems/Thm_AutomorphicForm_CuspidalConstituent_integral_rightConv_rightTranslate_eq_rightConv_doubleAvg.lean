-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_integral_rightConv_rightTranslate_eq_rightConv_doubleAvg
-- name    : AutomorphicForm.CuspidalConstituent.integral_rightConv_rightTranslate_eq_rightConv_doubleAvg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/062890a4-cae2-56d8-945d-2a10c1a8e87e
-- title:
--   χ-averaging a right convolution gives a doubly averaged test factor
-- statement:
--   Let $F$ be a number field and, for each infinite place $w$ of $F$, let $\chi_w$ be a homomorphism from the subgroup `rowIsometrySubgroup₀ w.Completion` of $\mathrm{GL}_2(F_w)$ to $\mathbb{C}^\times$ whose composite with the inclusion $\mathbb{C}^\times \hookrightarrow \mathbb{C}$ is continuous. Write $\mathcal{K} = \prod_w$ `rowIsometrySubgroup₀ w.Completion`, equipped with a Borel measurable structure, and let $\mu$ be a probability measure on $\mathcal{K}$ invariant under both left and right translation. Let $\iota : \mathcal{K} \to \mathrm{GL}_2(F_\infty)$ be a homomorphism into $\mathrm{GL}_2$ of the infinite adele ring such that for all $\kappa$ and $w$ the $w$-component `archComponent F w (ι κ)` equals the image of $\kappa_w$ in $\mathrm{GL}_2(F_w)$. Let $\Psi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be continuous and lie in `archCutSubmodule F (ArchTypeFamily.ofChar F χ)`, the intersection over the infinite places $w$ of the submodules `archTypeSubmoduleAt F w` attached to the one-dimensional representation `charRep (χ w)`; thus $\Psi$ is of archimedean type $\chi$. Let $f_\infty$ satisfy `IsArchTestFactor`, i.e. $f_\infty(g) = \Phi(\text{archEntries } g)$ for some $C^\infty$ function $\Phi$ on $2\times 2$ matrices over the mixed space of $F$, with $f_\infty$ compactly supported, and let $f_{\mathrm{f}}$ on $\mathrm{GL}_2$ of the finite adeles be locally constant with compact support. Setting $(\varphi * f)(g) = \int \varphi(g y) f(y)\,dy$ for the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$ (`rightConv`), and $f(y) = f_\infty(\text{glArch } y)\, f_{\mathrm{f}}(\text{glFin } y)$, the conclusion is the equality of functions of $x \in \mathrm{GL}_2(\mathbb{A}_F)$ $$\int_{\mathcal{K}} \Bigl(\prod_w \chi_w(\kappa_w)^{-1}\Bigr)\,(\Psi * f)\bigl(x \cdot \iota(\kappa)\bigr)\, d\mu(\kappa) = \bigl(\Psi * f'\bigr)(x),$$ where $\iota(\kappa)$ is pushed into $\mathrm{GL}_2(\mathbb{A}_F)$ by `adelicArchGLIncl` (identity at the finite part), and $f'(y) = f_\infty'(\text{glArch } y)\, f_{\mathrm{f}}(\text{glFin } y)$ with $$f_\infty'(z) = \iint_{\mathcal{K}\times\mathcal{K}} \Bigl(\prod_w \chi_w(\kappa_{1,w})^{-1}\Bigr)\Bigl(\prod_w \chi_w(\kappa_{2,w})^{-1}\Bigr) f_\infty\bigl(\iota(\kappa_1)^{-1} z\, \iota(\kappa_2)^{-1}\bigr)\, d(\mu\times\mu).$$
--
--   This is the compatibility of the $\chi$-isotypic projection along $\mathcal{K}$ with right convolution: averaging the right translates of a smoothed function $\Psi * f$ against $\chi^{-1}$ amounts to replacing the archimedean test factor by its two-sided $\chi^{-1}$-average, the finite factor being untouched. It is used in the analysis of cyclic spans of type-$\chi$ functions, feeding the statement that such a projection lands in the span of right translates together with the span of spherical right convolutions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_integral_rightConv_rightTranslate_eq_rightConv_doubleAvg.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.integral_rightConv_rightTranslate_eq_rightConv_doubleAvg
    (F : Type) [Field F] [NumberField F]
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hχ : ∀ w : InfinitePlace F, Continuous fun k : rowIsometrySubgroup₀ w.Completion => ((χ w k : ℂˣ) : ℂ))
    [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (Ψ : AdelicGL2 (𝓞 F) F → ℂ) (hΨ : Continuous Ψ)
    (hΨχ : Ψ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ))
    (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa : IsArchTestFactor F fa)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ) (hff : IsFinTestFactor F ff) :
    (fun x => ∫ κ, (∏ w, ((χ w (κ w)⁻¹ : ℂˣ) : ℂ)) *
        rightConv F Ψ (fun y => fa (AdelicLevel.glArch (𝓞 F) F y) * ff (AdelicLevel.glFin (𝓞 F) F y))
          (x * adelicArchGLIncl F (ι κ)) ∂μ)
      = rightConv F Ψ (fun y =>
          (fun y => ∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) ×
          (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
        (∏ w, ((χ w (p.1 w)⁻¹ : ℂˣ) : ℂ)) * (∏ w, ((χ w (p.2 w)⁻¹ : ℂˣ) : ℂ)) * fa ((ι p.1)⁻¹ * y * (ι p.2)⁻¹)
        ∂(μ.prod μ)) (AdelicLevel.glArch (𝓞 F) F y) * ff (AdelicLevel.glFin (𝓞 F) F y)) := by sorry
