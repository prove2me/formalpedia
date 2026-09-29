-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_Hom_bijective_map_and_forall_map_eq_of_isIso
-- name    : CerednikDrinfeld.FormalODModule.Hom.bijective_map_and_forall_map_eq_of_isIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/5af76796-6551-5bad-b9ad-e792535acf98
-- title:
--   Isomorphisms of formal mathcal O_D-modules induce graded Cartier isomorphisms
-- statement:
--   Fix a prime $p$ and a commutative ring $B$, together with a ring homomorphism $j \colon W(\mathbb F_{p^2}) \to B$, where $W(\mathbb F_{p^2})$ is the Witt vector ring [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17) of the field `GaloisField p 2`. Let $Y$ and $X$ be formal $\mathcal O_D$-modules over $B$ in the sense of the structure `FormalODModule`: each carries a commutative two-dimensional formal group law $F$, an additive and multiplicative action `act` of $W(\mathbb F_{p^2})$ by endomorphism power series, and an endomorphism series `varpi` with $\varpi \circ \varpi = \mathrm{act}(p)$ and $\varpi \circ \mathrm{act}(a) = \mathrm{act}(\sigma a) \circ \varpi$ for the Witt Frobenius $\sigma$. Let $u \colon Y \to X$ be a homomorphism of such modules, that is, a tuple of power series that is a homomorphism of formal group laws $Y.F \to X.F$ and commutes with the `act` operators and with `varpi`, and suppose $u$ is invertible: there is $v \colon X \to Y$ with $v \circ u$ and $u \circ v$ the respective identities. Let $g \colon \mathrm{Cart}_p(Y.F) \to \mathrm{Cart}_p(X.F)$ be an additive map assumed equal to the functorial map `CartierModule.map` associated with the underlying formal group law homomorphism `u.toLawHom`. Then: $g$ is bijective; $g(w \cdot m) = w \cdot g(m)$ for all $w \in W(B)$; $g$ commutes with `frobenius` and with `verschiebungInt`; $g$ intertwines the operators induced on the Cartier modules by the endomorphisms $Y.\varpi$ and $X.\varpi$ through `endAct`; and for every $i \in \mathbb N$, $g$ carries `Y.gradedPiece j i` into `X.gradedPiece j i`, where the $i$-th graded piece consists of those $f$ with $\mathrm{endAct}(\mathrm{act}(\tau(c)))\, f = \mathrm{homothety}\big(j(\tau(c))^{p^i}\big)\, f$ for all $c \in \mathbb F_{p^2}$, $\tau$ denoting the Teichmüller lift.
--
--   This is the functoriality of the Cartier module of a formal $\mathcal O_D$-module: an isomorphism of formal $\mathcal O_D$-modules induces an isomorphism of the associated Cartier modules respecting all the structure ($W(B)$-action, $F$, $V$, the operator coming from the uniformiser, and the grading attached to a ring homomorphism $j$). It is used by [`CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData`](thm.html#CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData), where the graded Cartier data attached to a formal $\mathcal O_D$-module is compared along isomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_Hom_bijective_map_and_forall_map_eq_of_isIso.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.Hom.bijective_map_and_forall_map_eq_of_isIso
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (Y X : CerednikDrinfeld.FormalODModule p B) (u : Y.Hom X) (hu : u.IsIso)
    (g : MvFormalGroup.CartierModule p Y.F →+ MvFormalGroup.CartierModule p X.F)
    (hg : g = MvFormalGroup.CartierModule.map u.toLawHom) :
    Function.Bijective g ∧
    (∀ (w : WittVector p B) (m : MvFormalGroup.CartierModule p Y.F),
      g (w • m) = w • g m) ∧
    (∀ m : MvFormalGroup.CartierModule p Y.F,
      g (MvFormalGroup.CartierModule.frobenius m) =
        MvFormalGroup.CartierModule.frobenius (g m)) ∧
    (∀ m : MvFormalGroup.CartierModule p Y.F,
      g (MvFormalGroup.CartierModule.verschiebungInt m) =
        MvFormalGroup.CartierModule.verschiebungInt (g m)) ∧
    (∀ m : MvFormalGroup.CartierModule p Y.F,
      g (MvFormalGroup.CartierModule.endAct Y.varpiEnd m) =
        MvFormalGroup.CartierModule.endAct X.varpiEnd (g m)) ∧
    (∀ (i : ℕ) (m : MvFormalGroup.CartierModule p Y.F),
      m ∈ Y.gradedPiece j i → g m ∈ X.gradedPiece j i) := by sorry
