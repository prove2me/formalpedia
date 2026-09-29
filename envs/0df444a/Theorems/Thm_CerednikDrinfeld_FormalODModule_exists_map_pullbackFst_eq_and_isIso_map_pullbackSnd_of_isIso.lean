-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_map_pullbackFst_eq_and_isIso_map_pullbackSnd_of_isIso
-- name    : CerednikDrinfeld.FormalODModule.exists_map_pullbackFst_eq_and_isIso_map_pullbackSnd_of_isIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/1b55fd87-26ca-5f8d-93d7-1cc03a636477
-- title:
--   Glueing formal 𝒪_D-modules along a fibre product of rings
-- statement:
--   Fix a prime $p$ and commutative rings $B$, $B'$, $B''$ together with ring homomorphisms $\varphi' \colon B' \to B$ and $\varphi'' \colon B'' \to B$, and assume $\varphi''$ is surjective with nilpotent kernel ideal. Let $X'$ and $X''$ be formal $\mathcal{O}_D$-modules over $B'$ and $B''$ respectively, i.e. data consisting of a two-dimensional commutative multivariate formal group law, a family of pairs of power series $\mathrm{act}(a)$ indexed by $a \in \mathbb{Z}_{p^2}$ and a further pair $\varpi$, each an endomorphism of the law, subject to $\mathrm{act}(1) = \mathrm{id}$, $\mathrm{act}(ab) = \mathrm{act}(a) \circ \mathrm{act}(b)$, additivity of $a \mapsto \mathrm{act}(a)$ with respect to the law, $\varpi \circ \varpi = \mathrm{act}(p)$ and $\varpi \circ \mathrm{act}(a) = \mathrm{act}(\sigma a) \circ \varpi$ with $\sigma$ the Frobenius. Let $w$ be a homomorphism of formal $\mathcal{O}_D$-modules over $B$ from the base change of $X'$ along $\varphi'$ to the base change of $X''$ along $\varphi''$ (base change being coefficientwise application of the map to all the defining series), and assume $w$ admits a two-sided inverse under composition. Write $P = \{(b',b'') \in B' \times B'' : \varphi'(b') = \varphi''(b'')\}$ for the fibre product subring, with its two projections `ModuliPackage.pullbackFst` and `ModuliPackage.pullbackSnd`. Then there exist a formal $\mathcal{O}_D$-module $X$ over $P$ and a homomorphism $\Psi$ from the base change of $X$ along the second projection to $X''$ such that the base change of $X$ along the first projection equals $X'$ (an equality of the data, not merely an isomorphism), $\Psi$ is an isomorphism, and the coefficientwise image of the series of $\Psi$ under $\varphi''$ is the series of $w$.
--
--   This is the glueing (effectivity of descent along a fibre product with one nilpotent surjective leg) step for formal $\mathcal{O}_D$-modules, as in the module part of Boutot–Carayol's treatment of the Čerednik–Drinfeld uniformisation. It is used in establishing the corresponding glueing property for rigidified special formal modules, which feeds the Schlessinger-type conditions for the associated moduli functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_map_pullbackFst_eq_and_isIso_map_pullbackSnd_of_isIso.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDescent
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.FormalODModule.exists_map_pullbackFst_eq_and_isIso_map_pullbackSnd_of_isIso
    (p : ℕ) [Fact p.Prime] {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hs'' : Function.Surjective φ'') (hn'' : IsNilpotent (RingHom.ker φ''))
    (X' : FormalODModule p B') (X'' : FormalODModule p B'')
    (w : (X'.map φ').Hom (X''.map φ'')) (hw : w.IsIso) :
    ∃ (X : FormalODModule p (ModuliPackage.pullbackRing φ' φ''))
      (Ψ : (X.map (ModuliPackage.pullbackSnd φ' φ'')).Hom X''),
      X.map (ModuliPackage.pullbackFst φ' φ'') = X' ∧ Ψ.IsIso ∧ Ψ.toSeries.map φ'' = w.toSeries := by sorry
