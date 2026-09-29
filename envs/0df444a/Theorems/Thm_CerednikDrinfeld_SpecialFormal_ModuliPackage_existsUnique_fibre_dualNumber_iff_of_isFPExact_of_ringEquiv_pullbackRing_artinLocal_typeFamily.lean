-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_existsUnique_fibre_dualNumber_iff_of_isFPExact_of_ringEquiv_pullbackRing_artinLocal_typeFamily
-- name    : CerednikDrinfeld.SpecialFormal.ModuliPackage.existsUnique_fibre_dualNumber_iff_of_isFPExact_of_ringEquiv_pullbackRing_artinLocal_typeFamily
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/94cbaf81-48b7-5b70-a42e-d8cfb778130f
-- title:
--   Fibres over a small extension match tangent vectors
-- statement:
--   Fix a prime $p$ and a commutative ring $O$. Let $F$ be given as a raw type family: for every commutative ring $B$ with a ring homomorphism $\psi : O \to B$ and a proof that $p$ is nilpotent in $B$, a type `Fobj B ψ`, together with transition maps `Fmap` along ring homomorphisms commuting with the structure maps, subject to the identity and composition laws `Fmap_id`, `Fmap_comp`. Assume the fibre-product exactness hypothesis `hF`: whenever $B,B',B''$ are Artinian local $O$-algebras in which $p$ is nilpotent and $\varphi' : B' \to B$, $\varphi'' : B'' \to B$ are surjections over $O$ with nilpotent kernels, and $p$ is nilpotent in the subring $B' \times_B B''$ of $B' \times B''$ cut out by $\varphi' \circ \mathrm{pr}_1 = \varphi'' \circ \mathrm{pr}_2$, then any $x' \in F(B')$, $x'' \in F(B'')$ with the same image in $F(B)$ come from a unique element of $F(B' \times_B B'')$. Let $k$ be a field, $B$ and $B'$ Artinian local rings, $\psi' : O \to B'$ a structure map with $p$ nilpotent in $B'$, $\varphi : B' \to B$ a surjection with nilpotent kernel, $\rho' : B' \to k$ a surjection with nilpotent kernel, $p$ nilpotent in $B$, in $k$ and in the dual numbers $k[\varepsilon] =$ `DualNumber k`, the latter carrying the structure map $O \to B' \to k \hookrightarrow k[\varepsilon]$ (the compatibility $\mathrm{pr}_1 \circ (k \to k[\varepsilon]) \circ \rho' \circ \psi' = \rho' \circ \psi'$ being `hfst`), with $p$ nilpotent in $B' \times_k k[\varepsilon]$ and in $B' \times_B B'$. Assume given a ring isomorphism $e : B' \times_B B' \to B' \times_k k[\varepsilon]$ commuting with the first projections, compatible with the two structure maps, and such that the second projection of $B' \times_B B'$ composed after $e^{-1}$ is again a map of $O$-algebras from $B' \times_k k[\varepsilon]$ to $B'$. Fix $x_0' \in F(B')$, and let $x \in F(B)$, $\bar x \in F(k)$ be its images under $\varphi$ and $\rho'$. Declare $x' \in F(B')$ related to $\tau \in F(k[\varepsilon])$ when there is $w \in F(B' \times_k k[\varepsilon])$ whose first projection is $x_0'$, whose image under the second projection of $B' \times_B B'$ composed after $e^{-1}$ is $x'$, and whose second projection is $\tau$. The conclusion is that this relation is the graph of a bijection between the fibre of $F(B') \to F(B)$ over $x$ and the fibre of $F(k[\varepsilon]) \to F(k)$ over $\bar x$: every $x'$ over $x$ is related to exactly one $\tau$ over $\bar x$, and every $\tau$ over $\bar x$ is related to exactly one $x'$ over $x$.
--
--   This is the Schlessinger-style comparison step: for a fibre-product-exact moduli functor on Artinian local rings in which $p$ is nilpotent, the fibres of a small surjection $B' \to B$ are parametrised by the tangent vectors $F(k[\varepsilon])$ above the residue point, the parametrisation being transported through a given isomorphism $B' \times_B B' \cong B' \times_k k[\varepsilon]$. It is stated for unbundled type families rather than for a bundled `ModuliPackage`, so that it can be applied with values in an arbitrary universe, and it feeds the bijectivity criterion [`CerednikDrinfeld.SpecialFormal.ModuliPackage.bijective_of_bijective_quotient_of_bijective_dualNumber_of_ringEquiv_pullbackRing_noetherian_artinLocal_typeFamily`](thm.html#CerednikDrinfeld.SpecialFormal.ModuliPackage.bijective_of_bijective_quotient_of_bijective_dualNumber_of_ringEquiv_pullbackRing_noetherian_artinLocal_typeFamily) in the study of deformations of special formal modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_existsUnique_fibre_dualNumber_iff_of_isFPExact_of_ringEquiv_pullbackRing_artinLocal_typeFamily.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDescent
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.SpecialFormal CerednikDrinfeld.SpecialFormal.ModuliPackage

universe u

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.existsUnique_fibre_dualNumber_iff_of_isFPExact_of_ringEquiv_pullbackRing_artinLocal_typeFamily
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O]
    (Fobj : ∀ (B : Type) [CommRing B] (ψ : O →+* B), IsNilpotent (p : B) → Type u)
    (Fmap : ∀ {B B' : Type} [CommRing B] [CommRing B'] {ψ : O →+* B} {ψ' : O →+* B'}
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B'),
      f.comp ψ = ψ' → Fobj B ψ hB → Fobj B' ψ' hB')
    (Fmap_id : ∀ {B : Type} [CommRing B] {ψ : O →+* B} (hB : IsNilpotent (p : B)) (x : Fobj B ψ hB),
      Fmap hB hB (RingHom.id B) (RingHom.id_comp ψ) x = x)
    (Fmap_comp : ∀ {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
      {ψ : O →+* B} {ψ' : O →+* B'} {ψ'' : O →+* B''}
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
      (g : B' →+* B'') (f : B →+* B') (hf : f.comp ψ = ψ') (hg : g.comp ψ' = ψ'') (x : Fobj B ψ hB),
      Fmap hB hB'' (g.comp f) (by rw [RingHom.comp_assoc, hf, hg]) x = Fmap hB' hB'' g hg (Fmap hB hB' f hf x))

    (hF : ∀ (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
      [IsLocalRing B] [IsLocalRing B'] [IsLocalRing B''] [IsArtinianRing B] [IsArtinianRing B'] [IsArtinianRing B'']
      (ψ : O →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
      (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
      (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
      (_ : Function.Surjective φ') (_ : Function.Surjective φ'')
      (_ : IsNilpotent (RingHom.ker φ')) (_ : IsNilpotent (RingHom.ker φ''))
      (hP : IsNilpotent (p : pullbackRing φ' φ'')),
      ∀ (x' : Fobj B' ψ' hB') (x'' : Fobj B'' ψ'' hB''),
        Fmap hB' hB φ' hφ' x' = Fmap hB'' hB φ'' hφ'' x'' →
        ∃! z : Fobj (pullbackRing φ' φ'') (pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)) hP,
          Fmap hP hB' (pullbackFst φ' φ'') (pullbackFst_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x' ∧
          Fmap hP hB'' (pullbackSnd φ' φ'') (pullbackSnd_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x'')
    (k : Type) [Field k]
    {B B' : Type} [CommRing B] [CommRing B'] [IsLocalRing B'] [IsArtinianRing B'] [IsLocalRing B] [IsArtinianRing B]
    (ψ' : O →+* B') (hB' : IsNilpotent (p : B'))
    (φ : B' →+* B) (hφ : Function.Surjective φ) (hφnil : IsNilpotent (RingHom.ker φ)) (hB : IsNilpotent (p : B))
    (ρ' : B' →+* k) (hρ' : Function.Surjective ρ') (hρ'nil : IsNilpotent (RingHom.ker ρ'))
    (hk : IsNilpotent (p : k)) (hkε : IsNilpotent (p : DualNumber k))

    (hfst : ((TrivSqZeroExt.fstHom k k k).toRingHom).comp ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) = ρ'.comp ψ')
    (hP : IsNilpotent (p : pullbackRing ρ' (TrivSqZeroExt.fstHom k k k).toRingHom))
    (hQ : IsNilpotent (p : pullbackRing φ φ))

    (e : pullbackRing φ φ ≃+* pullbackRing ρ' (TrivSqZeroExt.fstHom k k k).toRingHom)
    (he₁ : (pullbackFst ρ' (TrivSqZeroExt.fstHom k k k).toRingHom).comp e.toRingHom = pullbackFst φ φ)
    (heStr : e.toRingHom.comp (pullbackStr φ φ ψ' ψ' rfl) =
      pullbackStr ρ' (TrivSqZeroExt.fstHom k k k).toRingHom ψ' ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) hfst.symm)
    (hsnd : ((pullbackSnd φ φ).comp e.symm.toRingHom).comp
      (pullbackStr ρ' (TrivSqZeroExt.fstHom k k k).toRingHom ψ' ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) hfst.symm) = ψ')
    (x₀' : Fobj B' ψ' hB') :
    let P := pullbackRing ρ' (TrivSqZeroExt.fstHom k k k).toRingHom
    let ψP := pullbackStr ρ' (TrivSqZeroExt.fstHom k k k).toRingHom ψ' ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) hfst.symm
    let x := Fmap hB' hB φ rfl x₀'
    let xbar := Fmap hB' hk ρ' rfl x₀'
    let Rel : Fobj B' ψ' hB' → Fobj (DualNumber k) ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) hkε → Prop :=
      fun x' τ => ∃ w : Fobj P ψP hP,
        Fmap hP hB' (pullbackFst ρ' (TrivSqZeroExt.fstHom k k k).toRingHom)
          (pullbackFst_comp_pullbackStr ρ' _ ψ' _ hfst.symm) w = x₀' ∧
        Fmap hP hB' ((pullbackSnd φ φ).comp e.symm.toRingHom) hsnd w = x' ∧
        Fmap hP hkε (pullbackSnd ρ' (TrivSqZeroExt.fstHom k k k).toRingHom)
          (pullbackSnd_comp_pullbackStr ρ' _ ψ' _ hfst.symm) w = τ
    (∀ x' : Fobj B' ψ' hB', Fmap hB' hB φ rfl x' = x →
        ∃! τ : Fobj (DualNumber k) ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) hkε,
          Fmap hkε hk (TrivSqZeroExt.fstHom k k k).toRingHom hfst τ = xbar ∧ Rel x' τ) ∧
    (∀ τ : Fobj (DualNumber k) ((algebraMap k (DualNumber k)).comp (ρ'.comp ψ')) hkε,
        Fmap hkε hk (TrivSqZeroExt.fstHom k k k).toRingHom hfst τ = xbar →
        ∃! x' : Fobj B' ψ' hB', Fmap hB' hB φ rfl x' = x ∧ Rel x' τ) := by sorry
