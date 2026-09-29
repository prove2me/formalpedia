-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_eq_of_isCuspConstituent_of_exists_mem_ne_zero
-- name    : AutomorphicForm.CuspidalConstituent.eq_of_isCuspConstituent_of_exists_mem_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/1fb6cbcc-6454-581a-acfd-97722e20df56
-- title:
--   Cuspidal constituents sharing a nonzero vector coincide
-- statement:
--   Let $F$ be a number field, let `pins` be a bundle of carrier data on $\mathrm{GL}_2$ over the adeles of $F$ (a measurable space and a measure on $\mathrm{GL}_2(\mathbb{A}_F)$, a subset $D$, a subgroup $Z$ of the ideles, a family of level subgroups indexed by ideals of $\mathcal{O}_F$, local generators indexed by the height-one spectrum, and a measurable space and measure on the adele ring), and let $\xi \colon Z \to \mathbb{C}^\times$ be a monoid homomorphism into the units of $\mathbb{C}$. Let $V_1, V_2$ be $\mathbb{C}$-submodules of the space of functions $\mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$, each assumed to be a cuspidal constituent for $(F, \mathrm{pins}, \xi)$, i.e. each is a cuspidal subrepresentation — it is contained in `cuspKFiniteSubmodule F pins ξ`, it is stable under right translation by elements of the finite-adelic subgroup, under right translation by the images of the row-isometry subgroups at every infinite place of $F$, and under right convolution by every factorizable test function that is archimedean-bi-finite for some archimedean type family — and moreover each is nonzero and minimal among such cuspidal subrepresentations, in the sense that any cuspidal subrepresentation contained in it is either zero or equal to it. Assume there exists $\varphi$ in the intersection $V_1 \sqcap V_2$ with $\varphi \neq 0$. Then $V_1 = V_2$.
--
--   This is the elementary separation step underlying multiplicity one for the cuspidal spectrum of $\mathrm{GL}_2$: distinct irreducible cuspidal constituents meet in zero. It is used by the results on cuspidal constituents meeting a given space, phrased with covering of the group modulo the centre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_eq_of_isCuspConstituent_of_exists_mem_ne_zero.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.CuspidalConstituent.eq_of_isCuspConstituent_of_exists_mem_ne_zero
    (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (V₁ V₂ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (h₁ : AutomorphicForm.CuspidalConstituent.IsCuspConstituent F pins ξ V₁)
    (h₂ : AutomorphicForm.CuspidalConstituent.IsCuspConstituent F pins ξ V₂)
    (h : ∃ φ ∈ V₁ ⊓ V₂, φ ≠ 0) : V₁ = V₂ := by sorry
