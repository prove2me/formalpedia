-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_addEquiv_lieQuot_forall_apply_mkQ_eq_tangent
-- name    : CerednikDrinfeld.FormalODModule.exists_addEquiv_lieQuot_forall_apply_mkQ_eq_tangent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/db784b6f-35b1-5948-aa8b-e68da74d98a1
-- title:
--   Lie quotient M/VM identified with the tangent space
-- statement:
--   Let $p$ be a prime and let $B$ be a commutative ring of characteristic $p$, let $j\colon W(\mathbb{F}_{p^2}) \to B$ be a ring homomorphism, and let $X$ be a formal $\mathcal{O}_D$-module over $B$, i.e. a $2$-variable formal group law $F$ over $B$ together with a commutativity witness, an additive–multiplicative action of $W(\mathbb{F}_{p^2})$ by endomorphisms of $F$ and a further endomorphism $\varpi$ with $\varpi\circ\varpi$ the action of $p$ and $\varpi$ intertwining the action of $a$ with that of its Frobenius twist. Assume moreover `hc`, that the two graded pieces of $\mathrm{CartierModule}\,p\,X.F$ attached to $j$ in degrees $0$ and $1$ — the additive subgroups of those curves $f$ on which the action of the Teichmüller lift of each $c \in \mathbb{F}_{p^2}$ acts as the homothety by $j(\tau(c))^{p^n}$, $n = 0,1$ — are complementary. Then there exists an isomorphism $\Lambda$ of additive groups from the Lie quotient of the graded Cartier datum $X.\mathtt{toGradedCartierModuleData}\,j\,hc$, namely the quotient of $\mathrm{CartierModule}\,p\,X.F$ by the $W(B)$-submodule of values of the integral Verschiebung, onto $\mathrm{Fin}\,2 \to B$, such that $\Lambda$ of the class of any curve $m$ equals $\mathrm{tangent}\,m$ (the vector of coefficients of the first variable in the components of $m$), and such that $\Lambda(w \cdot q) = w_0 \, \Lambda(q)$ for all $w \in W(B)$ and all $q$ in the Lie quotient, where $w_0$ is the zeroth Witt coefficient of $w$.
--
--   This is the identification of the Lie quotient $M/VM$ of the Cartier module of a formal $\mathcal{O}_D$-module in characteristic $p$ with its tangent space $B^2$, the $W(B)$-action descending to multiplication through the zeroth Witt coefficient. It feeds the construction of the linear map on the Lie quotient used in the analysis of Cartier quadruples attached to rigidified special formal modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_addEquiv_lieQuot_forall_apply_mkQ_eq_tangent.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.FormalODModule.exists_addEquiv_lieQuot_forall_apply_mkQ_eq_tangent
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [CharP B p] (j : Zp2 p →+* B)
    (X : FormalODModule p B) (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1)) :
    ∃ Λ : (X.toGradedCartierModuleData j hc).LieQuot ≃+ (Fin 2 → B),
      (∀ m : MvFormalGroup.CartierModule p X.F,
          Λ ((X.toGradedCartierModuleData j hc).vRange.mkQ m) = MvFormalGroup.CartierModule.tangent m) ∧
      (∀ (w : WittVector p B) (q : (X.toGradedCartierModuleData j hc).LieQuot),
          Λ (w • q) = w.coeff 0 • Λ q) := by sorry
