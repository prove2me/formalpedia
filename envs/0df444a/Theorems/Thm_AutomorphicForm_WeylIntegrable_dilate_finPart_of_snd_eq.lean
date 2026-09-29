-- Prove2me | Theorems.Thm_AutomorphicForm_WeylIntegrable_dilate_finPart_of_snd_eq
-- name    : AutomorphicForm.WeylIntegrable.dilate_finPart_of_snd_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/c2996b12-69e0-5fca-9436-4032112255ce
-- title:
--   Dilated integral lattice depends only on the finite component
-- statement:
--   Let $F$ be a number field, and let $x,y$ be elements of the adele ring $\mathbb{A}=\mathbb{A}_F$, realised as a product so that $x.1$ is the archimedean and $x.2$ the finite component; assume $y.2=x.2$. For an adele with components $(a,b)$ one forms the element $\mathtt{selY}\,F\,a\,b$ of $\mathbb{A}$ together with the witness $\mathtt{selRel}\,F\,a\,b$ of the relation `SelRel` for it, i.e. of data $(\varepsilon,y,z,x)$ with $\varepsilon^2=\varepsilon$, $yz=1$, $(1-\varepsilon)y=1-\varepsilon$ and $\varepsilon y=\varepsilon x$; `yUnit` turns such a witness into the unit of $\mathbb{A}$ with underlying element $y$ and inverse $\varepsilon z+(1-\varepsilon)$, and `finPart` sends a unit $Y$ of $\mathbb{A}$ to the unit of the finite adele ring $\mathbb{A}_f$ with underlying element $Y.2$. Finally, for a unit $u$ of $\mathbb{A}_f$, $\mathtt{dilate}\,F\,u$ is the additive subgroup of $\mathbb{A}_f$ obtained as the image of the subgroup `intLattice` of integral finite adeles under multiplication by $u$. The assertion is the equality of additive subgroups $\mathtt{dilate}\,F(\mathtt{finPart}\,F(\mathtt{yUnit}(\mathtt{selRel}\,F\,y.1\,y.2)))=\mathtt{dilate}\,F(\mathtt{finPart}\,F(\mathtt{yUnit}(\mathtt{selRel}\,F\,x.1\,x.2)))$; that is, the dilate of $\widehat{\mathcal{O}}_F$ by the finite part of the selector unit is unchanged when the archimedean component of the adele is altered.
--
--   This is a bookkeeping lemma in the adelic analysis of the big Bruhat cell: the lattice $\mathbf{y}^\infty\widehat{\mathcal{O}}_F$ attached to an adele by the big-component selector reads only the finite component of that adele. It is used in the estimate [`AutomorphicForm.bruhatEisenstein_sub_constantTerm_isRapidlyDecreasingOn`](thm.html#AutomorphicForm.bruhatEisenstein_sub_constantTerm_isRapidlyDecreasingOn), where the archimedean variable moves while the finite data stay fixed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WeylIntegrable_dilate_finPart_of_snd_eq.lean

import Definitions.Def_AutomorphicForm_WeylSelectors

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.WeylIntegrable.dilate_finPart_of_snd_eq (F : Type) [Field F] [NumberField F]
    (x y : NumberField.AdeleRing (NumberField.RingOfIntegers F) F) (hy2 : y.2 = x.2) :
    dilate F (finPart F (yUnit (selRel F y.1 y.2))) = dilate F (finPart F (yUnit (selRel F x.1 x.2))) := by sorry
