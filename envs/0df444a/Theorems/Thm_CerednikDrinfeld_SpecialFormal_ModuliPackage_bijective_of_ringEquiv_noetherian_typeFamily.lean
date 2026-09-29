-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_bijective_of_ringEquiv_noetherian_typeFamily
-- name    : CerednikDrinfeld.SpecialFormal.ModuliPackage.bijective_of_ringEquiv_noetherian_typeFamily
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/b4b1b0c7-f314-57e9-90c3-b942e9abb5ae
-- title:
--   Transport of bijectivity along a ring isomorphism of test rings
-- statement:
--   Fix a prime $p$ (as a natural number carrying the primality fact) and a commutative ring $O$ in `Type`. Two moduli data are given in unbundled form, with values in arbitrary universes: a family `Gobj` assigning to every commutative ring $B$ in `Type`, every ring homomorphism $\psi : O \to B$ and every proof that the image of $p$ in $B$ is nilpotent a type in `Type u`, together with a transition map `Gmap` sending a ring homomorphism $f : B \to B'$ with $f \circ \psi = \psi'$ to a map $\mathrm{Gobj}\,B\,\psi \to \mathrm{Gobj}\,B'\,\psi'$, and hypotheses `Gmap_id` and `Gmap_comp` asserting that the identity homomorphism acts as the identity and that transition along $f$ followed by $g$ agrees with the composite of the transitions; and likewise a family `Hobj` with values in `Type v`, with `Hmap`, `Hmap_id`, `Hmap_comp`. Further given: a family $\xi$ of maps $\mathrm{Gobj}\,B\,\psi\,h_B \to \mathrm{Hobj}\,B\,\psi\,h_B$, defined for those $B$ which are Noetherian, and a naturality hypothesis $h\xi$ stating that for Noetherian $B, B'$ and $f : B \to B'$ with $f \circ \psi = \psi'$ one has $\xi(\mathrm{Gmap}\,f\,x) = \mathrm{Hmap}\,f\,(\xi\,x)$. Then, for Noetherian commutative rings $B$ and $C$ with $p$ nilpotent in each, a homomorphism $\psi : O \to B$ and a ring isomorphism $e : B \simeq C$, bijectivity of $\xi$ at $C$ with structure map $e \circ \psi$ implies bijectivity of $\xi$ at $B$ with structure map $\psi$.
--
--   This is the transport-along-isomorphism step for morphisms of moduli functors on Noetherian test rings with $p$ nilpotent, stated for functors presented as raw type families rather than bundled in the structure `ModuliPackage`, so that the source and target may take values in different universes. It is used in the Artin-style induction that reduces bijectivity of such a morphism to the Artinian and dual-number cases, and in the uniqueness-of-pullback statement for fake elliptic curves in the Cerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_bijective_of_ringEquiv_noetherian_typeFamily.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDescent
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.bijective_of_ringEquiv_noetherian_typeFamily
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]
    (Gobj : ∀ (B : Type) [CommRing B] (ψ : O →+* B), IsNilpotent (p : B) → Type u)
    (Gmap : ∀ {B B' : Type} [CommRing B] [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'}
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B'),
      f.comp ψ = ψ' → Gobj B ψ hB → Gobj B' ψ' hB')
    (Gmap_id : ∀ {B : Type} [CommRing B] {ψ : O →+* B} (hB : IsNilpotent (p : B)) (x : Gobj B ψ hB),
      Gmap hB hB (RingHom.id B) (RingHom.id_comp ψ) x = x)
    (Gmap_comp : ∀ {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
      {ψ : O →+* B} {ψ' : O →+* B'} {ψ'' : O →+* B''}
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
      (g : B' →+* B'') (f : B →+* B') (hf : f.comp ψ = ψ') (hg : g.comp ψ' = ψ'') (x : Gobj B ψ hB),
      Gmap hB hB'' (g.comp f) (by rw [RingHom.comp_assoc, hf, hg]) x = Gmap hB' hB'' g hg (Gmap hB hB' f hf x))
    (Hobj : ∀ (B : Type) [CommRing B] (ψ : O →+* B), IsNilpotent (p : B) → Type v)
    (Hmap : ∀ {B B' : Type} [CommRing B] [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'}
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B'),
      f.comp ψ = ψ' → Hobj B ψ hB → Hobj B' ψ' hB')
    (Hmap_id : ∀ {B : Type} [CommRing B] {ψ : O →+* B} (hB : IsNilpotent (p : B)) (x : Hobj B ψ hB),
      Hmap hB hB (RingHom.id B) (RingHom.id_comp ψ) x = x)
    (Hmap_comp : ∀ {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
      {ψ : O →+* B} {ψ' : O →+* B'} {ψ'' : O →+* B''}
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
      (g : B' →+* B'') (f : B →+* B') (hf : f.comp ψ = ψ') (hg : g.comp ψ' = ψ'') (x : Hobj B ψ hB),
      Hmap hB hB'' (g.comp f) (by rw [RingHom.comp_assoc, hf, hg]) x = Hmap hB' hB'' g hg (Hmap hB hB' f hf x))
    (ξ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)),
      Gobj B ψ hB → Hobj B ψ hB)
    (hξ : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B']
      (ψ : O →+* B) (ψ' : O →+* B') (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B'))
      (f : B →+* B') (hf : f.comp ψ = ψ') (x : Gobj B ψ hB),
      ξ B' ψ' hB' (Gmap hB hB' f hf x) = Hmap hB hB' f hf (ξ B ψ hB x))
    {B C : Type} [CommRing B] [CommRing C] [IsNoetherianRing B] [IsNoetherianRing C] (ψ : O →+* B) (hB : IsNilpotent (p : B)) (hC : IsNilpotent (p : C))
    (e : B ≃+* C) (h : Function.Bijective (ξ C (e.toRingHom.comp ψ) hC)) :
    Function.Bijective (ξ B ψ hB) := by sorry
