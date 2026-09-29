-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_mapPt_mul_and_factorsThrough_iff_of_isPushout_of_comp_eq_of_comp_eq
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.mapPt_mul_and_factorsThrough_iff_of_isPushout_of_comp_eq_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/222e079b-657e-527a-90f9-2a1e08b06c4d
-- title:
--   Comparison morphism of two gluings is a homomorphism
-- statement:
--   Fix $a,b\in\mathbb{Q}$ and a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$, a local ring $O$, and a level-$1$ fake elliptic curve $E_0$ over the residue field of $O$. Let $B,B',B''$ be Artinian local rings with maps $\psi,\psi',\psi''$ from $O$ and surjections $\rho,\rho',\rho''$ onto the residue field of $O$ whose kernels are the maximal ideals and which compose with the $\psi$'s to the residue map of $O$, and let $\varphi':B'\to B$, $\varphi'':B''\to B$ be surjections with nilpotent kernels, compatible with the $\psi$'s and the $\rho$'s. Let $E'$, $E''$, $E_B$ be level-$1$ fake elliptic curves over $B'$, $B''$, $B$ with morphisms $g',g'',g_B$ from $E_0.A$ exhibiting them as deformations of $E_0$ via $\rho',\rho'',\rho$ in the sense of `IsPullbackVia` (a pullback square of structure morphisms along the Spec of the ring map, together with compatibility of the morphism with the relative group law on $T$-points, with the $\Lambda$-action, and lifting of points factoring through the level morphism), and let $h':E_B.A\to E'.A$, $h'':E_B.A\to E''.A$ exhibit $E'$, $E''$ as deformations of $E_B$ via $\varphi'$, $\varphi''$, with $g_B\gg h'=g'$ and $g_B\gg h''=g''$. Over $P=\{(x,y)\in B'\times B'':\varphi'(x)=\varphi''(y)\}$ let $E$ and $\tilde E$ be level-$1$ fake elliptic curves, each deformation of $E_0$ via $\rho'\circ\mathrm{pullbackFst}$ (via $g$, resp. $\tilde g$) and each realising $E'$ and $E''$ via the two projections (through $k',k''$, resp. $\tilde k',\tilde k''$), subject to $g'\gg k'=g$, $h'\gg k'=h''\gg k''$, $g'\gg\tilde k'=\tilde g$, $g''\gg\tilde k''=\tilde g$, and with the square $(h',h'',k',k'')$ a pushout of schemes. Then for any morphism $u:E.A\to\tilde E.A$ over $P$ with $k'\gg u=\tilde k'$ and $k''\gg u=\tilde k''$: for every scheme $T$, every $t:T\to\operatorname{Spec}P$ and all $T$-points $P,Q$ of $E$ over $t$, post-composition with $u$ satisfies $u_*(P\cdot Q)=u_*P\cdot u_*Q$ for the respective relative group laws, and $P$ factors through $E.\mathrm{lev}$ if and only if $u_*P$ factors through $\tilde E.\mathrm{lev}$.
--
--   This is the rigidity step in the gluing (Schlessinger-type) argument for the deformation functor of level-$1$ fake elliptic curves over a fibre product of Artinian local rings: a morphism between two gluings compatible with the two realisations automatically respects the group law and the level morphism in both directions. It is used by [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_iso_of_isPushout_of_isPullbackVia_pullbackFst_pullbackSnd`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_iso_of_isPushout_of_isPullbackVia_pullbackFst_pullbackSnd), which produces an isomorphism of the two deformations over $B'\times_B B''$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_mapPt_mul_and_factorsThrough_iff_of_isPushout_of_comp_eq_of_comp_eq.lean

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

theorem CerednikDrinfeld.QM.FakeEllipticCurve.mapPt_mul_and_factorsThrough_iff_of_isPushout_of_comp_eq_of_comp_eq
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
    (hgkt' : g' ≫ kt' = gt) (hgkt'' : g'' ≫ kt'' = gt)

    (u : E.A ⟶ Et.A) (hu : u ≫ Et.f = E.f) (hk'u : k' ≫ u = kt') (hk''u : k'' ≫ u = kt'') :
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (P Q : SchemeHomOver t E.f),
        mapPt u hu (E.L.mul t P Q) = Et.L.mul t (mapPt u hu P) (mapPt u hu Q)) ∧
    (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) (P : SchemeHomOver t E.f),
        FactorsThrough E.lev P ↔ FactorsThrough Et.lev (mapPt u hu P)) := by sorry
