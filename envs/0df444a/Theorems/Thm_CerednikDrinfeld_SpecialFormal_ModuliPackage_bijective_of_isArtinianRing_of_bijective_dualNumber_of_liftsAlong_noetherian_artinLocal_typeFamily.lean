-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_bijective_of_isArtinianRing_of_bijective_dualNumber_of_liftsAlong_noetherian_artinLocal_typeFamily
-- name    : CerednikDrinfeld.SpecialFormal.ModuliPackage.bijective_of_isArtinianRing_of_bijective_dualNumber_of_liftsAlong_noetherian_artinLocal_typeFamily
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/2281a5d4-aa03-55f2-b395-ab8028b7b7e0
-- title:
--   Artinian bijectivity from residue field and dual numbers
-- statement:
--   Fix a prime $p$, a commutative ring $O$ and a field $k$ of characteristic $p$. Let $G$ and $H$ be given as raw families $\mathrm{Gobj}(B,\psi,h_B)$ in `Type u` and $\mathrm{Hobj}(B,\psi,h_B)$ in `Type v`, indexed by commutative rings $B$ together with a ring map $\psi\colon O\to B$ and a proof that $p$ is nilpotent in $B$, equipped with transition maps along ring maps $f\colon B\to B'$ satisfying $f\circ\psi=\psi'$ and subject to the identity and composition laws. Let $\xi_B\colon \mathrm{Gobj}(B,\psi,h_B)\to \mathrm{Hobj}(B,\psi,h_B)$ be given for Noetherian $B$ and compatible with all such transition maps between Noetherian rings ($h\xi$). Assume: (i) for all Artinian local $B,B',B''$ with structure maps, $p$ nilpotent in each, surjections $\varphi'\colon B'\to B$, $\varphi''\colon B''\to B$ compatible with the structure maps and with nilpotent kernels, and $p$ nilpotent in `pullbackRing` $\varphi'\,\varphi''$ — the subring of pairs in $B'\times B''$ with equal images in $B$, carrying the corestricted structure map — every pair of elements of $G$ (resp. $H$) over $B'$ and $B''$ with the same image over $B$ glues to a unique element over the pullback ring (hypotheses $hG$, $hH$); (ii) along every surjection $\varphi\colon B'\to B$ of Noetherian rings compatible with the structure maps whose kernel satisfies $\ker\varphi\cdot\ker\varphi=0$, an element $x$ of $G(B)$ lifts to $G(B')$ whenever $\xi_B(x)$ lifts to $H(B')$; (iii) $\xi_k$ is bijective for every ring map $O\to k$, and $\xi_{k[\varepsilon]}$ is bijective for the dual numbers over $k$ with structure map $O\to k\to k[\varepsilon]$. Then for every Artinian local commutative ring $B$ with structure map $\psi\colon O\to B$, $p$ nilpotent in $B$, admitting a surjection $\rho\colon B\to k$ with kernel the maximal ideal of $B$, the map $\xi_B$ is bijective.
--
--   This is the Artin-ring dévissage step for a morphism of moduli functors: bijectivity on the residue field and on its dual numbers, together with gluing over fibre products of Artinian local rings and lifting along square-zero extensions, forces bijectivity over all Artinian local rings with residue field $k$. It is the unbundled, universe-decoupled form of the corresponding statement for bundled moduli packages, and it feeds the comparison of formal moduli in the Cerednik–Drinfeld setting, in particular the pullback statement for fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_bijective_of_isArtinianRing_of_bijective_dualNumber_of_liftsAlong_noetherian_artinLocal_typeFamily.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDescent
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.bijective_of_isArtinianRing_of_bijective_dualNumber_of_liftsAlong_noetherian_artinLocal_typeFamily
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O]
    (k : Type) [Field k] [CharP k p]

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

    (hG : ∀ (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
      [IsLocalRing B] [IsLocalRing B'] [IsLocalRing B''] [IsArtinianRing B] [IsArtinianRing B'] [IsArtinianRing B'']
      (ψ : O →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
      (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
      (_ : Function.Surjective φ') (_ : Function.Surjective φ'')
      (_ : IsNilpotent (RingHom.ker φ')) (_ : IsNilpotent (RingHom.ker φ''))
      (hP : IsNilpotent (p : pullbackRing φ' φ'')),
      ∀ (x' : Gobj B' ψ' hB') (x'' : Gobj B'' ψ'' hB''),
        Gmap hB' hB φ' hφ' x' = Gmap hB'' hB φ'' hφ'' x'' →
        ∃! z : Gobj (pullbackRing φ' φ'') (pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)) hP,
          Gmap hP hB' (pullbackFst φ' φ'') (pullbackFst_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x' ∧
          Gmap hP hB'' (pullbackSnd φ' φ'') (pullbackSnd_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x'')
    (hH : ∀ (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
      [IsLocalRing B] [IsLocalRing B'] [IsLocalRing B''] [IsArtinianRing B] [IsArtinianRing B'] [IsArtinianRing B'']
      (ψ : O →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
      (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
      (_ : Function.Surjective φ') (_ : Function.Surjective φ'')
      (_ : IsNilpotent (RingHom.ker φ')) (_ : IsNilpotent (RingHom.ker φ''))
      (hP : IsNilpotent (p : pullbackRing φ' φ'')),
      ∀ (x' : Hobj B' ψ' hB') (x'' : Hobj B'' ψ'' hB''),
        Hmap hB' hB φ' hφ' x' = Hmap hB'' hB φ'' hφ'' x'' →
        ∃! z : Hobj (pullbackRing φ' φ'') (pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)) hP,
          Hmap hP hB' (pullbackFst φ' φ'') (pullbackFst_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x' ∧
          Hmap hP hB'' (pullbackSnd φ' φ'') (pullbackSnd_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x'')
    (hlift : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B']
      (ψ : O →+* B) (ψ' : O →+* B') (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B'))
      (φ : B' →+* B) (hφ : φ.comp ψ' = ψ) (_hφs : Function.Surjective φ)
      (_hφ2 : RingHom.ker φ * RingHom.ker φ = ⊥) (x : Gobj B ψ hB),
      (∃ y' : Hobj B' ψ' hB', Hmap hB' hB φ hφ y' = ξ B ψ hB x) → ∃ x' : Gobj B' ψ' hB', Gmap hB' hB φ hφ x' = x)

    (hpt : ∀ (ψk : O →+* k) (hk : IsNilpotent (p : k)), Function.Bijective (ξ k ψk hk))

    (htan : ∀ (ψk : O →+* k) (hkε : IsNilpotent (p : DualNumber k)),
      Function.Bijective (ξ (DualNumber k) ((algebraMap k (DualNumber k)).comp ψk) hkε))

    (B : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (ρ : B →+* k) (hρ : Function.Surjective ρ) (hρker : RingHom.ker ρ = IsLocalRing.maximalIdeal B) :
    Function.Bijective (ξ B ψ hB) := by sorry
