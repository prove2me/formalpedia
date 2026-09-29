-- Prove2me | Theorems.Thm_AlgebraicGeometry_TowerQuotientDatum_exists_sections_eq_of_forall_specMap_comp_eq
-- name    : AlgebraicGeometry.TowerQuotientDatum.exists_sections_eq_of_forall_specMap_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/3e5bb4a8-d910-55a6-8379-2d04ae351f69
-- title:
--   Descent of compatible chart functions along a tower quotient
-- statement:
--   Let $\mathcal{O}$ be a commutative ring, $\pi \in \mathcal{O}$, let $(X_n)_{n \in \mathbb{N}}$ be schemes equipped with structure morphisms $xb_n : X_n \to \operatorname{Spec}(\mathcal{O}/(\pi^{n+1}))$ and transitions $xt_n : X_n \to X_{n+1}$, let $G$ be a group acting by $a_n : G \to \operatorname{Aut}(X_n)$, and let $D$ be a `TowerQuotientDatum` for these data: schemes $Y_n$ with morphisms $yb_n : Y_n \to \operatorname{Spec}(\mathcal{O}/(\pi^{n+1}))$, proper and flat, transitions $yt_n : Y_n \to Y_{n+1}$ making each square over the quotient maps $\mathcal{O}/(\pi^{n+2}) \to \mathcal{O}/(\pi^{n+1})$ a pullback, and morphisms $p_n : X_n \to Y_n$ over the bases, compatible with the transitions (the square with $xt_n$, $yt_n$ being a pullback), invariant under $G$ ($a_n(g)$ followed by $p_n$ equals $p_n$), finite and surjective, epimorphic after restriction over each open of $Y_n$, together with a local universal property of $p_n$ for $G$-invariant morphisms on preimages of compatible opens; the remaining fields are summarised here. Assume in addition that the action commutes with the transitions: $a_n(g)$ followed by $xt_n$ equals $xt_n$ followed by $a_{n+1}(g)$. Let $A_n$ be commutative rings with ring maps $t_n : A_{n+1} \to A_n$, and let $\kappa_n : \operatorname{Spec} A_n \to X_n$ be open immersions with $\kappa_n$ followed by $xt_n$ equal to $\operatorname{Spec}(t_n)$ followed by $\kappa_{n+1}$. Let $U_n \subseteq Y_n$ be opens whose underlying sets are the images of the base maps of $\kappa_n$ followed by $p_n$, and which are compatible in the sense $yt_n^{-1}(U_{n+1}) = U_n$. Finally let $f_n \in A_n$ satisfy $t_n(f_{n+1}) = f_n$, and assume that for every $n$, every $g \in G$, every commutative ring $B$ and all ring maps $x, x' : A_n \to B$ such that $\operatorname{Spec}(x)$ followed by $\kappa_n$ equals $\operatorname{Spec}(x')$ followed by $\kappa_n$ followed by $a_n(g)$, one has $x(f_n) = x'(f_n)$. Then there exist sections $s_n \in \Gamma(U_n, Y_n)$ such that, for every $n$, the pullback of $s_{n+1}$ along $yt_n$ restricts on $U_n$ to $s_n$, and the pullback of $s_n$ along $\kappa_n$ followed by $p_n$, restricted to the whole of $\operatorname{Spec} A_n$, corresponds to $f_n$ under the canonical isomorphism $\Gamma(\operatorname{Spec} A_n) \cong A_n$.
--
--   This is the descent step for functions on a chart through the quotient morphisms $p_n : X_n \to Y_n$ of a tower quotient datum: a coherent family of chart functions that cannot distinguish a point from its $G$-translates comes from a coherent family of sections on the images of the charts in the quotient tower. It is used in the construction of functions on the unramified layers of the quotient tower, by [`CerednikDrinfeld.FormalOmega.descendedQuotientMap_nrFunctions_sections_of_inv`](thm.html#CerednikDrinfeld.FormalOmega.descendedQuotientMap_nrFunctions_sections_of_inv).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_TowerQuotientDatum_exists_sections_eq_of_forall_specMap_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TowerQuotientDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.TowerQuotientDatum.exists_sections_eq_of_forall_specMap_comp_eq
    {𝒪 : Type} [CommRing 𝒪] {π : 𝒪}
    {X : ℕ → Scheme.{0}} {xb : ∀ n : ℕ, X n ⟶ Spec (CommRingCat.of (𝒪 ⧸ Ideal.span {π ^ (n + 1)}))}
    {xt : ∀ n : ℕ, X n ⟶ X (n + 1)}
    {G : Type} [Group G] {a : ∀ n : ℕ, G →* Aut (X n)}
    (D : TowerQuotientDatum 𝒪 π X xb xt G a)
    (ha_xt : ∀ (n : ℕ) (g : G), (a n g).hom ≫ xt n = xt n ≫ (a (n + 1) g).hom)

    (A : ℕ → Type) [∀ n : ℕ, CommRing (A n)] (t : ∀ n : ℕ, A (n + 1) →+* A n)
    (κ : ∀ n : ℕ, Spec (CommRingCat.of (A n)) ⟶ X n) (hκ : ∀ n : ℕ, IsOpenImmersion (κ n))
    (hκt : ∀ n : ℕ, κ n ≫ xt n = Spec.map (CommRingCat.ofHom (t n)) ≫ κ (n + 1))

    (U : ∀ n : ℕ, (D.Y n).Opens)
    (hU : ∀ n : ℕ, (U n : Set (D.Y n)) = Set.range (κ n ≫ D.p n).base)
    (hUt : ∀ n : ℕ, (D.yt n) ⁻¹ᵁ (U (n + 1)) = U n)

    (fam : ∀ n : ℕ, A n) (hfam : ∀ n : ℕ, t n (fam (n + 1)) = fam n)
    (hagree : ∀ (n : ℕ) (g : G) (B : Type) [CommRing B] (x x' : A n →+* B),
      Spec.map (CommRingCat.ofHom x) ≫ κ n = (Spec.map (CommRingCat.ofHom x') ≫ κ n) ≫ (a n g).hom → x (fam n) = x' (fam n)) :
    ∃ s : ∀ n : ℕ, ↑((D.Y n).presheaf.obj (Opposite.op (U n))),
      (∀ (n : ℕ) (hle : U n ≤ (D.yt n) ⁻¹ᵁ (U (n + 1))),
        (D.Y n).presheaf.map (homOfLE hle).op (((D.yt n).app (U (n + 1))).hom (s (n + 1))) = s n) ∧
      ∀ (n : ℕ) (hle : (⊤ : (Spec (CommRingCat.of (A n))).Opens) ≤ (κ n ≫ D.p n) ⁻¹ᵁ (U n)),
        (Scheme.ΓSpecIso (CommRingCat.of (A n))).hom.hom
          ((Spec (CommRingCat.of (A n))).presheaf.map (homOfLE hle).op (((κ n ≫ D.p n).app (U n)).hom (s n))) = fam n := by sorry
