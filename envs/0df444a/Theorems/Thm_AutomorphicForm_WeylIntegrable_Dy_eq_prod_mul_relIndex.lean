-- Prove2me | Theorems.Thm_AutomorphicForm_WeylIntegrable_Dy_eq_prod_mul_relIndex
-- name    : AutomorphicForm.WeylIntegrable.Dy_eq_prod_mul_relIndex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/024c62e2-8e65-5413-b05d-3927bd50018c
-- title:
--   Modulus of the big-component idele: archimedean height times index
-- statement:
--   Let $F$ be a number field, with adele ring $\mathbb{A}=\mathbb{A}_F$ written as a pair consisting of an infinite part $x_\infty = x.1$ in the infinite adele ring and a finite part $x_f = x.2$ in the finite adele ring $\mathbb{A}_f$, and let $x\in\mathbb{A}$ be arbitrary; no further hypotheses are imposed. From the components of $x$ the term `selRel F x.1 x.2` produces data $\varepsilon,y,z$ satisfying the relations of `SelRel`, namely $\varepsilon^2=\varepsilon$, $yz=1$, $(1-\varepsilon)y=1-\varepsilon$ and $\varepsilon y=\varepsilon x$; `yUnit` turns these into the unit of $\mathbb{A}$ with value $y$ and inverse $\varepsilon z+(1-\varepsilon)$, and `Dy F x` is the real number $\mathrm{distribHaarChar}$ of that unit, i.e. the factor by which multiplication by it scales an additive Haar measure on $\mathbb{A}$. The assertion is that this modulus equals the product over the infinite places $w$ of $F$ of $\max(1,\|x_\infty(w)\|)^{m_w}$, where $m_w$ is `w.mult`, multiplied by the natural number, cast to $\mathbb{R}$, that is the relative index of the additive subgroup $\widehat{\mathcal O}$ of integral finite adeles (those whose component at each finite place lies in the valuation ring) inside its dilate $y_f\widehat{\mathcal O}$ by the finite-adelic part $y_f$ of that unit; Mathlib's `relIndex` here is the index of $\widehat{\mathcal O}\cap y_f\widehat{\mathcal O}$ in $y_f\widehat{\mathcal O}$.
--
--   This is the product formula for the modulus of the idele selected from an adele by taking, place by place, the component where it is large and $1$ elsewhere: the archimedean factor is a height, the non-archimedean factor an index of lattices of finite adeles. It feeds the convergence and decay estimates of the project, being used in [`AutomorphicForm.WeylIntegrable.rpow_Dy_le_translate_of_le`](thm.html#AutomorphicForm.WeylIntegrable.rpow_Dy_le_translate_of_le) and in the rapid decay of the Bruhat–Eisenstein series minus its constant term.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WeylIntegrable_Dy_eq_prod_mul_relIndex.lean

import Definitions.Def_AutomorphicForm_WeylSelectors

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.WeylIntegrable.Dy_eq_prod_mul_relIndex (F : Type) [Field F] [NumberField F]
    (x : NumberField.AdeleRing (NumberField.RingOfIntegers F) F) :
    Dy F x = (∏ w : NumberField.InfinitePlace F, (max 1 ‖x.1 w‖) ^ w.mult)
      * ((intLattice F).relIndex (dilate F (finPart F (yUnit (selRel F x.1 x.2)))) : ℝ) := by sorry
