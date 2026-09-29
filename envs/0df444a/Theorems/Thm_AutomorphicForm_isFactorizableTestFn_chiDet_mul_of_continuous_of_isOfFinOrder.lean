-- Prove2me | Theorems.Thm_AutomorphicForm_isFactorizableTestFn_chiDet_mul_of_continuous_of_isOfFinOrder
-- name    : AutomorphicForm.isFactorizableTestFn_chiDet_mul_of_continuous_of_isOfFinOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/ebfdff23-b877-5d6b-83a7-8f8dc39b99c3
-- title:
--   Factorizable test functions are stable under twisting by η∘det
-- statement:
--   Let $F$ be a number field, let $\eta \colon (\mathbb{A}_F)^{\times} \to \mathbb{C}^{\times}$ be a group homomorphism from the units of the adele ring of $F$ (formed with respect to $\mathcal{O}_F$) to $\mathbb{C}^{\times}$, assumed continuous and of finite order, and let $f \colon \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ satisfy `IsFactorizableTestFn F f`, that is: there are functions $f_\infty$ on $\mathrm{GL}_2$ of the infinite adele ring and $f_{\mathrm{fin}}$ on $\mathrm{GL}_2$ of the finite adele ring such that (i) $f_\infty$ is of the form $g \mapsto \Phi(\mathrm{archEntries}\,g)$ for some $\Phi$ on $2\times 2$ matrices over the mixed space of $F$ which is $C^\infty$ over $\mathbb{R}$, and $f_\infty$ has compact support; (ii) $f_{\mathrm{fin}}$ is locally constant with compact support; and (iii) $f(g) = f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ for all $g$, where `glArch` and `glFin` are the maps on $\mathrm{GL}_2$ induced by the projections of the adeles to the infinite and finite adeles. The conclusion is that the function $g \mapsto \eta(\det g)\, f(g)$, with $\eta(\det g)$ the complex number $\mathrm{chiDet}$ attaches to $\eta$, again satisfies `IsFactorizableTestFn F`. No condition of triviality of $\eta$ on $F^{\times}$ is imposed.
--
--   This is the elementary stability of the space of pure-tensor test functions on $\mathrm{GL}_2(\mathbb{A}_F)$ under twisting by a finite-order idele class character composed with the determinant. It is used in the construction of twisted central-character constituents, namely by [`AutomorphicForm.CuspidalConstituent.isCuspConstituent_twistedCentralChar_span_image_fnTwist`](thm.html#AutomorphicForm.CuspidalConstituent.isCuspConstituent_twistedCentralChar_span_image_fnTwist).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isFactorizableTestFn_chiDet_mul_of_continuous_of_isOfFinOrder.lean

import Mathlib
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open AutomorphicForm

theorem AutomorphicForm.isFactorizableTestFn_chiDet_mul_of_continuous_of_isOfFinOrder
    (F : Type) [Field F] [NumberField F]
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hηc : Continuous η) (hηo : IsOfFinOrder η)
    (f : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hf : IsFactorizableTestFn F f) :
    IsFactorizableTestFn F (fun g => chiDet (𝓞 F) F η g * f g) := by sorry
