-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_lieZero_lieOne_map_eq_span_image
-- name    : CerednikDrinfeld.FormalODModule.lieZero_lieOne_map_eq_span_image
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/dd99467b-6891-5bf7-bae1-d0e7524eaf4b
-- title:
--   Base change of the graded pieces of Lie
-- statement:
--   Fix a prime $p$, commutative rings $B$ and $S$ in a common universe, a ring homomorphism $j \colon \mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2}) \to B$ (here $\mathbb{Z}_{p^2}$ is [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17), the Witt vectors of the field $\mathbb{F}_{p^2}$), a ring homomorphism $g \colon B \to S$, and a formal $\mathcal{O}_D$-module $X$ over $B$, i.e. a $2$-dimensional commutative formal group law $X.F$ over $B$ together with an action `act` of $\mathbb{Z}_{p^2}$ by endomorphisms of the law and an endomorphism `varpi` of the law satisfying `varpi.comp varpi = act p` and `varpi.comp (act a) = (act (WittVector.frobenius a)).comp varpi`. The tangent module $X.\mathrm{Lie}$ is the $B$-module $B^2 = (\mathrm{Fin}\ 2 \to B)$, on which each $a \in \mathbb{Z}_{p^2}$ induces a $B$-linear endomorphism `X.lieAct a`; the submodules $X.\mathrm{lieZero}\ j$ and $X.\mathrm{lieOne}\ j$ are $\bigcap_{a} \ker(\mathrm{lieAct}\ a - j(a)\cdot \mathrm{id})$ and $\bigcap_{a} \ker(\mathrm{lieAct}\ a - j(\varphi(a))\cdot \mathrm{id})$ respectively, $\varphi$ denoting the Witt vector Frobenius. Let $X.\mathrm{map}\ g$ be the formal $\mathcal{O}_D$-module over $S$ obtained by applying $g$ to the coefficients of the group law, of each `act a` and of `varpi`, and let $B^2 \to S^2$, $m \mapsto (i \mapsto g(m\,i))$, be the coordinatewise map on tangent modules. The theorem asserts two things. First, the $S$-span of the image of $X.\mathrm{lieZero}\ j$ is contained in $(X.\mathrm{map}\ g).\mathrm{lieZero}\ (g \circ j)$, and likewise the $S$-span of the image of $X.\mathrm{lieOne}\ j$ is contained in $(X.\mathrm{map}\ g).\mathrm{lieOne}\ (g \circ j)$. Second, if $X.\mathrm{lieZero}\ j$ and $X.\mathrm{lieOne}\ j$ are complementary submodules of $B^2$, then both inclusions are equalities.
--
--   This is the compatibility of the eigenspace decomposition of the tangent module of a formal $\mathcal{O}_D$-module with base change along $B \to S$, in the form used in the Čerednik–Drinfeld uniformisation: the graded pieces of $\mathrm{Lie}$ always map into the corresponding pieces after base change, and they generate them once the two pieces split $\mathrm{Lie}$, as happens for special formal modules. It is used in the construction of free bases for the base-changed pieces and in the semilinear tangent data attached to rigidified special formal modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_lieZero_lieOne_map_eq_span_image.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.lieZero_lieOne_map_eq_span_image
    (p : ℕ) [Fact p.Prime] {B S : Type u} [CommRing B] [CommRing S] (j : CerednikDrinfeld.Zp2 p →+* B)
    (g : B →+* S) (X : CerednikDrinfeld.FormalODModule p B) :
    (Submodule.span S ((fun m : X.Lie => fun i => g (m i)) '' (X.lieZero j : Set X.Lie)) ≤
        (X.map g).lieZero (g.comp j) ∧
      Submodule.span S ((fun m : X.Lie => fun i => g (m i)) '' (X.lieOne j : Set X.Lie)) ≤
        (X.map g).lieOne (g.comp j)) ∧
    (IsCompl (X.lieZero j) (X.lieOne j) →
      Submodule.span S ((fun m : X.Lie => fun i => g (m i)) '' (X.lieZero j : Set X.Lie)) =
          (X.map g).lieZero (g.comp j) ∧
        Submodule.span S ((fun m : X.Lie => fun i => g (m i)) '' (X.lieOne j : Set X.Lie)) =
          (X.map g).lieOne (g.comp j)) := by sorry
