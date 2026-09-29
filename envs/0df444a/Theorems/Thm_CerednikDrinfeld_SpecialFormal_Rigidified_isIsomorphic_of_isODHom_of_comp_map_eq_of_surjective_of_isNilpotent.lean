-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_isODHom_of_comp_map_eq_of_surjective_of_isNilpotent
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.isIsomorphic_of_isODHom_of_comp_map_eq_of_surjective_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/33211fa1-3482-5d72-bea8-b953305fe480
-- title:
--   Rigidity of rigidification compatibility under nilpotent thickenings
-- statement:
--   Fix a prime $p$, a commutative ring $O$ with a ring homomorphism $\iota \colon \mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2}) \to O$, and a formal $O_D$-module $\Phi$ over $O/pO$. Let $\pi \colon R \to S$ be a surjective homomorphism of commutative rings whose kernel is a nilpotent ideal, let $p$ be nilpotent in $R$, and let $\psi \colon O \to R$ be a ring homomorphism. Let $t_1 = (X_1, n_1, \rho_1)$ and $t_2 = (X_2, n_2, \rho_2)$ be rigidified objects over $R$ — each consisting of a formal $O_D$-module over $R$, a natural number, and a pair of power series over $R/pR$ — both admissible in the sense that $X_i$ is special for the structure map `structureMap` built from $\iota$ and $\psi$, has height $4$, and $\rho_i$ is an isogeny of height $4n_i$ from $\Phi$ based changed to $R/pR$ to the reduction $X_i \bmod p$. Let $u, v$ be pairs of power series over $R$ with $u$ an $O_D$-homomorphism $X_1 \to X_2$ and $v$ an $O_D$-homomorphism $X_2 \to X_1$ (i.e. homomorphisms of the underlying formal groups commuting with the $\mathbb{Z}_{p^2}$-action and with $\varpi$), mutually inverse for substitution: $v \circ u = u \circ v = \mathrm{id}$. Suppose for some $m \in \mathbb{N}$ the identity $[p^{m+n_2}] \circ \bar u \circ \bar\rho_1 = [p^{m+n_1}] \circ \bar\rho_2$ holds after base change along $\pi$, i.e. over $S/pS$, where $[p^k]$ denotes the action of $p^k$ on $X_2 \bmod p$ over $S$. Then $t_1$ and $t_2$ are isomorphic as rigidified objects over $R$: there are mutually inverse $O_D$-homomorphisms between $X_1$ and $X_2$ and an exponent $m'$ with $[p^{m'+n_2}] \circ \bar u \circ \bar\rho_1 = [p^{m'+n_1}] \circ \bar\rho_2$ already over $R/pR$.
--
--   This is the uniqueness (rigidity) step in the Čerednik–Drinfeld theory of special formal $O_D$-modules with rigidification: compatibility of an $O_D$-isomorphism with the rigidifications can be descended from a nilpotent thickening quotient at the cost of enlarging the exponent of $p$. It is used in the construction and gluing arguments for rigidified special formal modules, for instance in the identification of fibre products and in the transport of rigidifications along correspondences for fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isIsomorphic_of_isODHom_of_comp_map_eq_of_surjective_of_isNilpotent.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.Rigidified.isIsomorphic_of_isODHom_of_comp_map_eq_of_surjective_of_isNilpotent
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O) {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    {R S : Type} [CommRing R] [CommRing S]
    (π : R →+* S) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π)) (hR : IsNilpotent (p : R))
    (ψ : O →+* R) (t₁ t₂ : Rigidified p Φ R) (h₁ : t₁.IsAdmissible ι ψ) (h₂ : t₂.IsAdmissible ι ψ)
    (u v : Series R) (hu : FormalODModule.IsODHom t₁.X t₂.X u) (hv : FormalODModule.IsODHom t₂.X t₁.X v)
    (hvu : v.comp u = Series.id R) (huv : u.comp v = Series.id R) (m : ℕ)
    (hc : ((t₂.map π).Xbar.act ((p : Zp2 p) ^ (m + t₂.n))).comp
        (((u.map π).map (Ideal.Quotient.mk (pIdeal p S))).comp (t₁.map π).ρ)
      = ((t₂.map π).Xbar.act ((p : Zp2 p) ^ (m + t₁.n))).comp (t₂.map π).ρ) :
    t₁.IsIsomorphic t₂ := by sorry
