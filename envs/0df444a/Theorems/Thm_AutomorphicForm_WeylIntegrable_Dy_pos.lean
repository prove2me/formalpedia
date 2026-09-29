-- Prove2me | Theorems.Thm_AutomorphicForm_WeylIntegrable_Dy_pos
-- name    : AutomorphicForm.WeylIntegrable.Dy_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/e315e533-8608-538e-9e5f-e1e4160b2774
-- title:
--   Positivity of the adelic modulus D_y
-- statement:
--   Let $F$ be a number field, with ring of integers $\mathcal{O}_F$ and adele ring $\mathbb{A} = \mathbb{A}_F$, realised as the product of the infinite adeles and the finite adeles, so that an adele $x$ has components $x.1$ and $x.2$. For such an $x$, the real number $D_y(F,x)$ (`Dy F x`) is defined as the value of the distributive Haar character `distribHaarChar` of $\mathbb{A}$ — the factor by which multiplication by a unit rescales an additive Haar measure on $\mathbb{A}$ — evaluated at the unit of $\mathbb{A}$ obtained by `yUnit` from the datum `selRel F x.1 x.2` of the relation `SelRel` attached to the infinite and finite components of $x$; concretely, for a quadruple $(\varepsilon, y, z, x)$ satisfying `SelRel`, `yUnit` is the unit with underlying element $y$ and inverse $\varepsilon z + (1-\varepsilon)$, and the real number is the coercion to $\mathbb{R}$ of the nonnegative real value of the character. The assertion is that $0 < D_y(F,x)$ for every adele $x$; there are no hypotheses on $x$.
--
--   The quantity $D_y$ is the modulus of the distinguished idele selected from an adele by the Weyl selectors, and this lemma records that it is a strictly positive real number, so that real powers $D_y^{-a}$ behave as powers of a positive base. It is used in [`AutomorphicForm.WeylIntegrable.rpow_Dy_le_translate_of_le`](thm.html#AutomorphicForm.WeylIntegrable.rpow_Dy_le_translate_of_le) and in the rapid-decay estimate [`AutomorphicForm.bruhatEisenstein_sub_constantTerm_isRapidlyDecreasingOn`](thm.html#AutomorphicForm.bruhatEisenstein_sub_constantTerm_isRapidlyDecreasingOn).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WeylIntegrable_Dy_pos.lean

import Definitions.Def_AutomorphicForm_WeylSelectors

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.WeylIntegrable.Dy_pos (F : Type) [Field F] [NumberField F]
    (x : NumberField.AdeleRing (NumberField.RingOfIntegers F) F) : 0 < Dy F x := by sorry
