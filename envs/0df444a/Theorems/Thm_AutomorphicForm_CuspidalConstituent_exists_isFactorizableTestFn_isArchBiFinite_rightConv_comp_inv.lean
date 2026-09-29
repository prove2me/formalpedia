-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_rightConv_comp_inv
-- name    : AutomorphicForm.CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_rightConv_comp_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/084511c2-f2bf-5207-99d4-f7eb609d7a4e
-- title:
--   Convolution f'*check f of factorizable bi-finite test functions
-- statement:
--   Let $F$ be a number field, and let $f,f' : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be functions on the adelic general linear group of rank $2$ over $F$. Let $\mathrm{tys},\mathrm{tys}'$ be archimedean type families over $F$, each consisting of a cardinality $\mathrm{card}(w) \in \mathbb{N}$ for every infinite place $w$ together with, for each $w$ and each index $i < \mathrm{card}(w)$, a complex representation of $\mathtt{rowIsometrySubgroup₀}$ of the completion at $w$ on some $\mathbb{C}^n$. Assume both $f$ and $f'$ satisfy `IsFactorizableTestFn`, i.e. each factors as $g \mapsto f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ where $f_\infty$ is compactly supported and of the form $\Phi \circ \mathtt{archEntries}$ for some smooth $\Phi$ on $2\times2$ matrices over the mixed space of $F$, and $f_{\mathrm{fin}}$ is locally constant with compact support; assume moreover $f$ is $\mathrm{tys}$-bi-finite and $f'$ is $\mathrm{tys}'$-bi-finite, in the sense that $x \mapsto f(x^{-1})$ lies in the archimedean type cut submodule of the given family and $f$ itself lies in the dual cut submodule, and similarly for $f'$. Then there is an archimedean type family $\mathrm{tys}''$ over $F$ such that the function $g \mapsto \int f'(gx)\,f(x^{-1})\,dx$, the integral being against the Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$ for its Borel structure, is again a factorizable test function and is bi-finite of type family $\mathrm{tys}''$.
--
--   This is the closure property of the space of factorizable, archimedean-bi-finite test functions on $\mathrm{GL}_2(\mathbb{A}_F)$ under the operation $(f,f') \mapsto f' * \check f$ with $\check f(x) = f(x^{-1})$, in the precise shape needed to rewrite $(\varphi * f) * f'$ as $\varphi * (f' * \check f)$. It is used in the construction of cuspidal constituents, where a cyclic span under right convolution is shown to be a subrepresentation of the cusp space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_isFactorizableTestFn_isArchBiFinite_rightConv_comp_inv.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_rightConv_comp_inv
    (F : Type) [Field F] [NumberField F]
    (f f' : AdelicGL2 (𝓞 F) F → ℂ) (tys tys' : ArchTypeFamily F)
    (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys f)
    (hf' : IsFactorizableTestFn F f') (hbf' : IsArchBiFinite F tys' f') :
    ∃ tys'' : ArchTypeFamily F,
      IsFactorizableTestFn F (rightConv F f' (fun x => f x⁻¹)) ∧
      IsArchBiFinite F tys'' (rightConv F f' (fun x => f x⁻¹)) := by sorry
