-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_isIsomorphic_eta_eq_of_isODHom_comp_eq_id
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_isIsomorphic_eta_eq_of_isODHom_comp_eq_id
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/720e465d-5b0e-5756-a742-0f2fbf2a01b2
-- title:
--   Transporting an admissible rigidification along an isomorphism
-- statement:
--   Let $p$ be a prime, $O$ a commutative ring with a ring homomorphism $\iota : \mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2}) \to O$, let $\Phi$ be a formal $\mathcal{O}_D$-module over $O/pO$ (a commutative two-dimensional formal group law together with a $\mathbb{Z}_{p^2}$-action and a series $\varpi$ satisfying the relations of `FormalODModule`), and let $M$ be a moduli package over $O$. Let $\eta$ assign, to every commutative ring $B$ with a homomorphism $\psi : O \to B$ and $p$ nilpotent in $B$, a map from rigidified objects $t = (t.X, t.n, t.\rho)$ over $B$ to $M.\mathrm{obj}\,B\,\psi$, and assume that over Noetherian $B$ and for $(\iota,\psi)$-admissible $t, t'$ one has $\eta(t) = \eta(t')$ if and only if `t.IsIsomorphic t'`. Fix a Noetherian $B$ with $\chi : O \to B$ and $p$ nilpotent in $B$, formal $\mathcal{O}_D$-modules $X, X'$ over $B$, and series $u, v$ over $B$ that are $\mathcal{O}_D$-homomorphisms $X \to X'$ and $X' \to X$ (homomorphisms of the formal group laws commuting with the $\mathbb{Z}_{p^2}$-action and with $\varpi$) which are mutually inverse under substitution. Let $t'$ be a rigidified object with $t'.X = X'$ that is admissible for $(\iota,\chi)$, that is: $X'$ is special for $\chi \circ \iota$ (the $\chi\iota$-eigenspaces of the Lie algebra are complementary and invertible), $X'$ has height $4$, and $t'.\rho$ is an isogeny of height $4\,t'.n$ from the reduction of $\Phi$ determined by $\chi$ to $X' \bmod pB$. Assume further that $X$ is special for $\chi \circ \iota$ and has height $4$. Then there exists a rigidified object $t$ over $B$ with $t.X = X$, $t.n = t'.n$ and $t.\rho$ obtained by substituting $t'.\rho$ into the reduction of $v$ modulo $pB$, such that $t$ is admissible for $(\iota,\chi)$, `t'.IsIsomorphic t` and `t.IsIsomorphic t'` both hold, and $\eta(t) = \eta(t')$.
--
--   This is the re-basing step for rigidified special formal $\mathcal{O}_D$-modules: an isomorphism $X \cong X'$ of formal $\mathcal{O}_D$-modules transports an admissible rigidification on $X'$ to one on $X$ with the same exponent and the same point of the moduli package. It is used in the treatment of rigidifications of fake elliptic curves, where Drinfeld translate relations and Atkin–Lehner comparisons require two rigidified triples to be compared on a single formal module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_isIsomorphic_eta_eq_of_isODHom_comp_eq_id.lean

import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_isIsomorphic_eta_eq_of_isODHom_comp_eq_id
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O) {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    {M : ModuliPackage.{0, 0} p O}
    (η : ∀ (B : Type) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)), Rigidified p Φ B → M.obj B ψ hB)
    (hη : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
        (t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
        (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t'))

    (B : Type) [CommRing B] [IsNoetherianRing B] (χ : O →+* B) (hBp : IsNilpotent (p : B))
    (X X' : FormalODModule p B) (u v : Series B)
    (hu : FormalODModule.IsODHom X X' u) (hv : FormalODModule.IsODHom X' X v)
    (hvu : v.comp u = Series.id B) (huv : u.comp v = Series.id B)
    (t' : Rigidified p Φ B) (ht'X : t'.X = X') (hadm' : t'.IsAdmissible ι χ)
    (hXs : X.IsSpecial (structureMap ι χ)) (hX4 : X.HasHeight 4) :
    ∃ t : Rigidified p Φ B,
      t.X = X ∧ t.n = t'.n ∧
      t.ρ = (Series.map (Ideal.Quotient.mk (pIdeal p B)) v).comp t'.ρ ∧
      t.IsAdmissible ι χ ∧ t'.IsIsomorphic t ∧ t.IsIsomorphic t' ∧
      η B χ hBp t = η B χ hBp t' := by sorry
