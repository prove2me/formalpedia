-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_pullbackRing_of_isPullbackVia_of_isArtinianRing
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_pullbackRing_of_isPullbackVia_of_isArtinianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/f8905902-c344-5927-81c8-97f142cb1f5d
-- title:
--   Fibre-product exactness for deformations of a fake elliptic curve
-- statement:
--   Let $a,b\in\mathbb{Q}$, let $\Lambda$ be a $\mathbb{Z}$-submodule of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, let $O$ be a local ring and let $E_0$ be a fake elliptic curve of level $1$ over the residue field of $O$ (a scheme with a relative commutative group law, the abelian-scheme property bundle, two-dimensional fibres, an action of $\Lambda$ and a level structure). Let $B$, $B'$, $B''$ be Artinian local rings with ring maps $\psi,\psi',\psi''$ from $O$ and surjections $\rho,\rho',\rho''$ onto the residue field of $O$ whose kernels are the respective maximal ideals and which compose with $\psi,\psi',\psi''$ to the residue map of $O$; let $\varphi':B'\to B$ and $\varphi'':B''\to B$ be surjective with nilpotent kernels, compatible with the $\psi$'s and with the $\rho$'s ($\varphi'\circ\psi'=\psi$, $\rho\circ\varphi'=\rho'$, and likewise for $\varphi''$). Assume given fake elliptic curves $E'$ over $B'$, $E''$ over $B''$ and $E_B$ over $B$ of level $1$, together with morphisms $g':E_0.A\to E'.A$, $g'':E_0.A\to E''.A$, $g_B:E_0.A\to E_B.A$ exhibiting $E_0$ as the base change of $E'$, $E''$, $E_B$ along $\rho'$, $\rho''$, $\rho$ respectively in the sense of `IsPullbackVia` (cartesian square of structure morphisms, compatibility with the group law on $T$-points, with the $\Lambda$-action, and transport of level-structure factorisations), morphisms $h':E_B.A\to E'.A$ and $h'':E_B.A\to E''.A$ exhibiting $E_B$ as the base change of $E'$ along $\varphi'$ and of $E''$ along $\varphi''$ in the same sense, and the compatibilities $g_B$ followed by $h'$ equal to $g'$ and $g_B$ followed by $h''$ equal to $g''$. Then over the fibre-product ring $B'\times_B B''$ (the subring of pairs $(x,y)$ with $\varphi'(x)=\varphi''(y)$) there exist a fake elliptic curve $E$ of level $1$, a morphism $g:E_0.A\to E.A$ exhibiting $E_0$ as the base change of $E$ along $\rho'\circ\mathrm{pr}_1$, and morphisms $k':E'.A\to E.A$, $k'':E''.A\to E.A$ exhibiting $E'$ and $E''$ as the base changes of $E$ along the two projections, such that $g'$ followed by $k'$ and $g''$ followed by $k''$ both equal $g$, and $h'$ followed by $k'$ equals $h''$ followed by $k''$. Moreover such data are unique up to isomorphism: for any $E_t$ over $B'\times_B B''$ with $g_t$, $k_t'$, $k_t''$ satisfying the same pullback conditions and $g'$ followed by $k_t'$ equal to $g_t$, $g''$ followed by $k_t''$ equal to $g_t$, there is an isomorphism $e:E.A\cong E_t.A$ over $\mathrm{Spec}(B'\times_B B'')$ which is a homomorphism for the relative group laws on $T$-points, commutes with the $\Lambda$-actions, matches the level structures in the sense that a $T$-point factors through $E.\mathrm{lev}$ if and only if its image factors through $E_t.\mathrm{lev}$, and satisfies $g$ followed by $e$ equal to $g_t$.
--
--   This is Schlessinger's fibre-product exactness condition for the rigidified deformation functor of a level-$1$ fake elliptic curve over the residue field of $O$, stated directly in terms of fake elliptic curves, `IsPullbackVia` and the fibre-product ring rather than through a packaged functor of Artin rings. It is used in the construction of deformations over towers, feeding the statement that pullback data over power-series-type bases exist uniquely.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isPullbackVia_pullbackRing_of_isPullbackVia_of_isArtinianRing.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_pullbackRing_of_isPullbackVia_of_isArtinianRing
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
    (hgh' : gB ≫ h' = g') (hgh'' : gB ≫ h'' = g'') :
    ∃ (E : FakeEllipticCurve Λ 1 (pullbackRing φ' φ'')) (g : E₀.A ⟶ E.A)
      (_ : FakeEllipticCurve.IsPullbackVia (ρ'.comp (pullbackFst φ' φ'')) E E₀ g)
      (k' : E'.A ⟶ E.A) (_ : FakeEllipticCurve.IsPullbackVia (pullbackFst φ' φ'') E E' k')
      (k'' : E''.A ⟶ E.A) (_ : FakeEllipticCurve.IsPullbackVia (pullbackSnd φ' φ'') E E'' k''),
      g' ≫ k' = g ∧ g'' ≫ k'' = g ∧ h' ≫ k' = h'' ≫ k'' ∧

      ∀ (Et : FakeEllipticCurve Λ 1 (pullbackRing φ' φ'')) (gt : E₀.A ⟶ Et.A)
        (_ : FakeEllipticCurve.IsPullbackVia (ρ'.comp (pullbackFst φ' φ'')) Et E₀ gt)
        (kt' : E'.A ⟶ Et.A) (_ : FakeEllipticCurve.IsPullbackVia (pullbackFst φ' φ'') Et E' kt')
        (kt'' : E''.A ⟶ Et.A) (_ : FakeEllipticCurve.IsPullbackVia (pullbackSnd φ' φ'') Et E'' kt''),
        g' ≫ kt' = gt → g'' ≫ kt'' = gt →
        ∃ (e : E.A ≅ Et.A) (he : e.hom ≫ Et.f = E.f),
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (P Q : SchemeHomOver t E.f),
            mapPt e.hom he (E.L.mul t P Q) = Et.L.mul t (mapPt e.hom he P) (mapPt e.hom he Q)) ∧
          (∀ x : ↥Λ, E.act x ≫ e.hom = e.hom ≫ Et.act x) ∧
          (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (P : SchemeHomOver t E.f),
            FactorsThrough E.lev P ↔ FactorsThrough Et.lev (mapPt e.hom he P)) ∧
          g ≫ e.hom = gt := by sorry
