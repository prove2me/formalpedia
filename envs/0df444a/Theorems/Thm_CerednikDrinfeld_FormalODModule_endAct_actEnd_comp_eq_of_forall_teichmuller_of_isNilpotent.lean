-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_endAct_actEnd_comp_eq_of_forall_teichmuller_of_isNilpotent
-- name    : CerednikDrinfeld.FormalODModule.endAct_actEnd_comp_eq_of_forall_teichmuller_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/c3ab187c-63bb-5fc1-9966-54af9d815dfd
-- title:
--   Teichmüller equivariance implies full ℤ_{p²}-equivariance of Cartier modules
-- statement:
--   Fix a prime $p$ and a commutative ring $B$ in which the image of $p$ is nilpotent. Let $X$ and $X'$ be formal $\mathcal{O}_D$-modules over $B$ in the sense of the project: each consists of a two-dimensional formal group law over $B$ together with a proof of its commutativity, a family `act` of pairs of power series indexed by $\mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2})$ and a further pair `varpi`, all of which are homomorphisms of the law (constant coefficients zero, compatible with the group law), such that `act 1` is the identity substitution, `act` turns products into composition and sums into addition via the group law, `varpi` composed with itself is `act` at $p$, and `varpi` composed with `act a` equals `act` at the Witt–Frobenius of $a$ composed with `varpi`. For $a \in \mathbb{Z}_{p^2}$ write $X.\mathrm{actEnd}\,a$ for the resulting endomorphism of the formal group law, and let it act on the Cartier module of the law — families of power series in countably many variables with vanishing constant term satisfying the Witt-addition compatibility — through the ring homomorphism [`MvFormalGroup.CartierModule.endAct`](def/MvFormalGroup_CartierModule.html#L782). Let $\theta$ be an additive map from the Cartier module of $X$ to that of $X'$ such that for every $c \in \mathbb{F}_{p^2}$ and every element $f$ of the source, $\theta$ commutes with the action of the Teichmüller lift of $c$. Then $\theta$ commutes with the action of every $a \in \mathbb{Z}_{p^2}$, on every element $f$.
--
--   This is the rigidity step in Cartier-theoretic descriptions of special formal $\mathcal{O}_D$-modules: equivariance for the unramified part of the action needs only be checked on Teichmüller representatives. It is used in the construction of a bijective map of Cartier modules in the analysis of Cartier quadruples attached to rigidified special formal modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_endAct_actEnd_comp_eq_of_forall_teichmuller_of_isNilpotent.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.FormalODModule.endAct_actEnd_comp_eq_of_forall_teichmuller_of_isNilpotent
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (hB : IsNilpotent (p : B))
    (X X' : FormalODModule p B)
    (θ : MvFormalGroup.CartierModule p X.F →+ MvFormalGroup.CartierModule p X'.F)
    (hθ : ∀ (c : GaloisField p 2) (f : MvFormalGroup.CartierModule p X.F),
      θ (MvFormalGroup.CartierModule.endAct (X.actEnd (WittVector.teichmuller p c)) f) =
        MvFormalGroup.CartierModule.endAct (X'.actEnd (WittVector.teichmuller p c)) (θ f)) :
    ∀ (a : Zp2 p) (f : MvFormalGroup.CartierModule p X.F),
      θ (MvFormalGroup.CartierModule.endAct (X.actEnd a) f) =
        MvFormalGroup.CartierModule.endAct (X'.actEnd a) (θ f) := by sorry
