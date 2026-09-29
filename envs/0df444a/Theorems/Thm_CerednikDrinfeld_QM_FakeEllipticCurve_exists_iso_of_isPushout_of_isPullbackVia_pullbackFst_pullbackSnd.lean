-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_iso_of_isPushout_of_isPullbackVia_pullbackFst_pullbackSnd
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_iso_of_isPushout_of_isPullbackVia_pullbackFst_pullbackSnd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/ec8619c0-ce4f-55d8-8898-487eac6ed3bd
-- title:
--   Uniqueness of the glued fake elliptic curve over B'×_B B''
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$, a local ring $O$, and a level-$1$ fake elliptic curve $E_0$ over the residue field of $O$. Let $B,B',B''$ be Artinian local rings with ring maps $\psi,\psi',\psi''$ from $O$ and surjections $\rho,\rho',\rho''$ onto the residue field of $O$ whose kernels are the respective maximal ideals and which compose with $\psi,\psi',\psi''$ to the residue map of $O$, and let $\varphi':B'\to B$, $\varphi'':B''\to B$ be surjections over $O$ with nilpotent kernels, compatible with the $\rho$'s. Let $E'$, $E''$, $E_B$ be level-$1$ fake elliptic curves over $B'$, $B''$, $B$ equipped with morphisms $g',g'',g_B$ from $E_0.A$ exhibiting $E_0$ as the base change along $\rho',\rho'',\rho$ in the sense of `IsPullbackVia` (a pullback square of structure morphisms, compatibility with the relative group laws on $T$-points, commutation with the $\Lambda$-action, and liftability of points factoring through the level morphism), and with morphisms $h':E_B.A\to E'.A$, $h'':E_B.A\to E''.A$ exhibiting $E_B$ as the base change of $E'$ along $\varphi'$ and of $E''$ along $\varphi''$ in the same sense, with $g_B$ followed by $h'$ equal to $g'$ and $g_B$ followed by $h''$ equal to $g''$. Write $P$ for the fibre-product ring $\{(x,y)\in B'\times B'' : \varphi'(x)=\varphi''(y)\}$ with its two projections. Let $E$ be a level-$1$ fake elliptic curve over $P$ with $g:E_0.A\to E.A$ exhibiting $E_0$ as base change along $\rho'\circ\mathrm{pr}'$, and $k':E'.A\to E.A$, $k'':E''.A\to E.A$ exhibiting $E'$, $E''$ as base changes along the two projections, such that $g'$ followed by $k'$ is $g$, $h'$ followed by $k'$ equals $h''$ followed by $k''$, and $(k',k'')$ makes $E.A$ the pushout of $h'$ and $h''$. Let $\tilde E$, $\tilde g$, $\tilde k'$, $\tilde k''$ satisfy the same pullback conditions over $P$, with $g'$ followed by $\tilde k'$ and $g''$ followed by $\tilde k''$ both equal to $\tilde g$. Then there is an isomorphism of schemes $e:E.A\cong\tilde E.A$ over $\operatorname{Spec} P$ (i.e. $e$ followed by $\tilde E.f$ is $E.f$) which is a homomorphism for the relative group laws on $T$-points for every scheme $T$ over $\operatorname{Spec} P$, commutes with the actions of all $x\in\Lambda$, has the property that a $T$-point of $E$ factors through $E.\mathrm{lev}$ precisely when its image factors through $\tilde E.\mathrm{lev}$, and satisfies: $k'$ followed by $e$ is $\tilde k'$, $k''$ followed by $e$ is $\tilde k''$, and $g$ followed by $e$ is $\tilde g$.
--
--   This is the uniqueness half of the fibre-product (Schlessinger-type) exactness property for the deformation functor of level-$1$ fake elliptic curves: a gluing of $E'$ and $E''$ over $B'\times_B B''$ whose total space is the pushout of the two restrictions is unique up to isomorphism respecting the group law, the quaternionic action, the level structure and all the structural morphisms. It is used in the construction of a deformation over $B'\times_B B''$ restricting to given ones over $B'$ and $B''$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_iso_of_isPushout_of_isPullbackVia_pullbackFst_pullbackSnd.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open IsLocalRing
open CategoryTheory CategoryTheory.Limits CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal CerednikDrinfeld.SpecialFormal.ModuliPackage NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_iso_of_isPushout_of_isPullbackVia_pullbackFst_pullbackSnd
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (O : Type) [CommRing O] [IsLocalRing O]
    (E₀ : FakeEllipticCurve Λ 1 (ResidueField O))

    (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
    [IsLocalRing B] [IsLocalRing B'] [IsLocalRing B''] [IsArtinianRing B] [IsArtinianRing B'] [IsArtinianRing B'']
    (ψ : O →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
    (ρ : B →+* ResidueField O) (ρ' : B' →+* ResidueField O) (ρ'' : B'' →+* ResidueField O)
    (hρ : Function.Surjective ρ) (hρ' : Function.Surjective ρ') (hρ'' : Function.Surjective ρ'')
    (hρker : RingHom.ker ρ = maximalIdeal B) (hρ'ker : RingHom.ker ρ' = maximalIdeal B') (hρ''ker : RingHom.ker ρ'' = maximalIdeal B'')
    (hρψ : ρ.comp ψ = residue O) (hρ'ψ : ρ'.comp ψ' = residue O) (hρ''ψ : ρ''.comp ψ'' = residue O)
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
    (hφ'ρ : ρ.comp φ' = ρ') (hφ''ρ : ρ.comp φ'' = ρ'')
    (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
    (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))

    (E' : FakeEllipticCurve Λ 1 B') (g' : E₀.A ⟶ E'.A) (hg' : FakeEllipticCurve.IsPullbackVia ρ' E' E₀ g')
    (E'' : FakeEllipticCurve Λ 1 B'') (g'' : E₀.A ⟶ E''.A) (hg'' : FakeEllipticCurve.IsPullbackVia ρ'' E'' E₀ g'')

    (EB : FakeEllipticCurve Λ 1 B) (gB : E₀.A ⟶ EB.A) (hgB : FakeEllipticCurve.IsPullbackVia ρ EB E₀ gB)
    (h' : EB.A ⟶ E'.A) (hh' : FakeEllipticCurve.IsPullbackVia φ' E' EB h')
    (h'' : EB.A ⟶ E''.A) (hh'' : FakeEllipticCurve.IsPullbackVia φ'' E'' EB h'')
    (hgh' : gB ≫ h' = g') (hgh'' : gB ≫ h'' = g'')

    (E : FakeEllipticCurve Λ 1 (pullbackRing φ' φ'')) (g : E₀.A ⟶ E.A)
    (hg : FakeEllipticCurve.IsPullbackVia (ρ'.comp (pullbackFst φ' φ'')) E E₀ g)
    (k' : E'.A ⟶ E.A) (hk' : FakeEllipticCurve.IsPullbackVia (pullbackFst φ' φ'') E E' k')
    (k'' : E''.A ⟶ E.A) (hk'' : FakeEllipticCurve.IsPullbackVia (pullbackSnd φ' φ'') E E'' k'')
    (hgk' : g' ≫ k' = g) (hhk : h' ≫ k' = h'' ≫ k'') (hpo : IsPushout h' h'' k' k'')

    (Et : FakeEllipticCurve Λ 1 (pullbackRing φ' φ'')) (gt : E₀.A ⟶ Et.A)
    (hgt : FakeEllipticCurve.IsPullbackVia (ρ'.comp (pullbackFst φ' φ'')) Et E₀ gt)
    (kt' : E'.A ⟶ Et.A) (hkt' : FakeEllipticCurve.IsPullbackVia (pullbackFst φ' φ'') Et E' kt')
    (kt'' : E''.A ⟶ Et.A) (hkt'' : FakeEllipticCurve.IsPullbackVia (pullbackSnd φ' φ'') Et E'' kt'')
    (hgkt' : g' ≫ kt' = gt) (hgkt'' : g'' ≫ kt'' = gt) :
    ∃ (e : E.A ≅ Et.A) (he : e.hom ≫ Et.f = E.f),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (P Q : SchemeHomOver t E.f),
        mapPt e.hom he (E.L.mul t P Q) = Et.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
      (∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ Et.act x) ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (P : SchemeHomOver t E.f),
        FactorsThrough E.lev P ↔ FactorsThrough Et.lev (mapPt e.hom he P)) ∧
      k' ≫ e.hom = kt' ∧ k'' ≫ e.hom = kt'' ∧ g ≫ e.hom = gt := by sorry
