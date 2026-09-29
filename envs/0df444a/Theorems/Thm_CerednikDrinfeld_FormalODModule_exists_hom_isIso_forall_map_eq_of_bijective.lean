-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_hom_isIso_forall_map_eq_of_bijective
-- name    : CerednikDrinfeld.FormalODModule.exists_hom_isIso_forall_map_eq_of_bijective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/f4bf6461-ac74-5af8-adc8-f2efb4ebe09e
-- title:
--   Cartier-module isomorphisms come from formal mathcal O_D-module isomorphisms
-- statement:
--   Let $p$ be a prime and $B$ a commutative ring, equipped with a ring homomorphism $j$ from [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17), the Witt vectors of the field with $p^2$ elements, into $B$ (this serves only to make $B$ an algebra over $\mathbb Z_p$, via $\mathbb Z_p \cong W(\mathbb F_p) \to W(\mathbb F_{p^2}) \to B$). Let $X$ and $X'$ be formal $\mathcal O_D$-modules over $B$ in the sense of [`CerednikDrinfeld.FormalODModule`](def/CerednikDrinfeld_SpecialFormalModule.html#L170): each consists of a two-dimensional commutative formal group law, a family of endomorphisms $\mathrm{act}(a)$ indexed by $a \in$ `Zp2 p` which is multiplicative for composition, additive for the group law and sends $1$ to the identity, together with an endomorphism $\varpi$ satisfying $\varpi \circ \varpi = \mathrm{act}(p)$ and $\varpi \circ \mathrm{act}(a) = \mathrm{act}(\sigma a) \circ \varpi$ for the Witt-vector Frobenius $\sigma$. Let $\theta$ be an additive map from the Cartier module of $X.F$ to that of $X'.F$ (tuples of power series in the variables indexed by $\mathbb N$ with zero constant term, compatible with the Witt addition laws) which is bijective and commutes with the Frobenius operator, with the integral Verschiebung operator, with the homothety by every $b \in B$, with the operator induced by $\mathrm{act}(a)$ for every $a$, and with the operator induced by $\varpi$. Then there exists a homomorphism $u : X \to X'$ of formal $\mathcal O_D$-modules (a law homomorphism commuting with all $\mathrm{act}(a)$ and with $\varpi$) admitting a two-sided inverse, such that the map on Cartier modules induced by the underlying law homomorphism of $u$ agrees with $\theta$ on every element.
--
--   This is the full-faithfulness half of Cartier theory in the form used for formal $\mathcal O_D$-modules over a general $\mathbb Z_{p^2}$-algebra base: an isomorphism of Cartier modules respecting $F$, $V$, the homotheties and the $\mathcal O_D$-action descends to an isomorphism of the formal $\mathcal O_D$-modules themselves. It is the general-base input for recognising two formal $\mathcal O_D$-modules as isomorphic through their Cartier modules, and is used in the derivation of the corresponding criterion phrased in terms of structure constants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_hom_isIso_forall_map_eq_of_bijective.lean

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

theorem CerednikDrinfeld.FormalODModule.exists_hom_isIso_forall_map_eq_of_bijective
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (X X' : CerednikDrinfeld.FormalODModule p B)
    (θ : MvFormalGroup.CartierModule p X.F →+ MvFormalGroup.CartierModule p X'.F)
    (hθ : Function.Bijective θ)
    (hF : ∀ f, θ (MvFormalGroup.CartierModule.frobenius f) =
      MvFormalGroup.CartierModule.frobenius (θ f))
    (hV : ∀ f, θ (MvFormalGroup.CartierModule.verschiebungInt f) =
      MvFormalGroup.CartierModule.verschiebungInt (θ f))
    (hH : ∀ (b : B) f, θ (MvFormalGroup.CartierModule.homothety b f) =
      MvFormalGroup.CartierModule.homothety b (θ f))
    (hA : ∀ (a : CerednikDrinfeld.Zp2 p) f,
      θ (MvFormalGroup.CartierModule.endAct (X.actEnd a) f) =
        MvFormalGroup.CartierModule.endAct (X'.actEnd a) (θ f))
    (hPi : ∀ f, θ (MvFormalGroup.CartierModule.endAct X.varpiEnd f) =
      MvFormalGroup.CartierModule.endAct X'.varpiEnd (θ f)) :
    ∃ u : X.Hom X', u.IsIso ∧
      ∀ f, MvFormalGroup.CartierModule.map u.toLawHom f = θ f := by sorry
