-- Prove2me | Theorems.Thm_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor
-- name    : AutomorphicForm.isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/0be5b280-7669-58ce-a984-c5c2a8ac6ac7
-- title:
--   Two-sided χ-averaging of an archimedean test factor
-- statement:
--   Let $F$ be a number field. For each infinite place $w$ of $F$ let $\chi_w$ be a group homomorphism from the group `rowIsometrySubgroup₀ w.Completion` $\subseteq \mathrm{GL}_2(F_w)$ to $\mathbb{C}^\times$, and assume each $\chi_w$ is continuous as a $\mathbb{C}$-valued function. Write $\mathcal{K} = \prod_{w \mid \infty}$ `rowIsometrySubgroup₀ w.Completion`, equipped with a measurable structure that is the Borel structure of its topology, and let $\mu$ be a finite measure on $\mathcal{K}$ invariant under both left and right translations. Let $\iota : \mathcal{K} \to \mathrm{GL}_2(\mathbb{A}_{F,\infty})$ be a group homomorphism such that for all $\kappa$ and all $w$ the $w$-component `archComponent F w (ι κ)`, obtained by applying $\iota\kappa$ entrywise through evaluation at $w$, equals the image of $\kappa_w$ in $\mathrm{GL}_2(F_w)$. Let $f_a : \mathrm{GL}_2(\mathbb{A}_{F,\infty}) \to \mathbb{C}$ satisfy `IsArchTestFactor F`, i.e. $f_a$ has compact support and there is a $C^\infty$ function $\Phi$ on $2\times 2$ matrices over the mixed space of $F$ with $f_a(g) = \Phi(\mathrm{archEntries}\,F\,g)$, where `archEntries` transports the entries of $g$ along the ring equivalence of the infinite adele ring with the mixed space. Put
--   $$f_a'(y) = \int_{\mathcal{K}\times\mathcal{K}} \Bigl(\prod_w \chi_w(p_{1,w})^{-1}\Bigr)\Bigl(\prod_w \chi_w(p_{2,w})^{-1}\Bigr) f_a\bigl(\iota(p_1)^{-1}\, y\, \iota(p_2)^{-1}\bigr)\, d(\mu\times\mu)(p_1,p_2).$$
--   Then $f_a'$ again satisfies `IsArchTestFactor F`, and `IsArchFactorBiFinite F (ArchTypeFamily.ofChar F χ) f_a'` holds: that is, $y \mapsto f_a'(y^{-1})$ lies in the intersection over all infinite places $w$ of the submodules `archFactorTypeSubmoduleAt F w (ArchRepAt.ofChar F (χ w))` (the family `ArchTypeFamily.ofChar F χ` has one type at each place, namely the one-dimensional representation `charRep (χ w)` of `rowIsometrySubgroup₀ w.Completion` on $\mathrm{Fin}\,1 \to \mathbb{C}$), and $f_a'$ itself lies in the corresponding intersection of the dual submodules `archFactorDualTypeSubmoduleAt F w (ArchRepAt.ofChar F (χ w))`.
--
--   This is the two-sided isotypic averaging of a smooth compactly supported archimedean test function on $\mathrm{GL}_2(F_\infty)$ against the one-dimensional type $\chi = (\chi_w)_w$ of the archimedean compact group, performed simultaneously in the left and the right variable. It supplies the archimedean input for the isotypic-projection statement [`AutomorphicForm.CuspidalConstituent.mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar`](thm.html#AutomorphicForm.CuspidalConstituent.mem_span_rightTranslate_sup_span_rightConv_spherical_of_mem_span_cyclic_of_mem_archCutSubmodule_ofChar), where convolution by a pure tensor test function is replaced by convolution by its $\chi$-averaged archimedean factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel AutomorphicForm

theorem AutomorphicForm.isArchTestFactor_and_isArchFactorBiFinite_ofChar_integral_of_isArchTestFactor
    (F : Type) [Field F] [NumberField F]
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (hχ : ∀ w : InfinitePlace F, Continuous fun k : rowIsometrySubgroup₀ w.Completion => ((χ w k : ℂˣ) : ℂ))
    [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hfa : IsArchTestFactor F fa) :
    IsArchTestFactor F (fun y => ∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) ×
          (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
        (∏ w, ((χ w (p.1 w)⁻¹ : ℂˣ) : ℂ)) * (∏ w, ((χ w (p.2 w)⁻¹ : ℂˣ) : ℂ)) * fa ((ι p.1)⁻¹ * y * (ι p.2)⁻¹)
        ∂(μ.prod μ)) ∧
    IsArchFactorBiFinite F (ArchTypeFamily.ofChar F χ) (fun y => ∫ p : (∀ w : InfinitePlace F,
          rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
        (∏ w, ((χ w (p.1 w)⁻¹ : ℂˣ) : ℂ)) * (∏ w, ((χ w (p.2 w)⁻¹ : ℂˣ) : ℂ)) * fa ((ι p.1)⁻¹ * y * (ι p.2)⁻¹)
        ∂(μ.prod μ)) := by sorry
