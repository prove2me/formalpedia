-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuli_exists_iso_pullback_awayD
-- name    : CerednikDrinfeld.QM.IsCoarseModuli.exists_iso_pullback_awayD
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/a3823abc-14fb-5e0d-8a34-d28f4c68dcad
-- title:
--   Uniqueness of the coarse moduli curve over ℚ̄
-- statement:
--   Fix a nonzero natural number $N$, rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, and a natural number $D$; write $R = \mathbb{Z}[1/D]$ for `Localization.Away ((D : ℕ) : ℤ)`. Let $\bar F$ be a field over $\bar{\mathbb{Q}} =$ `AlgebraicClosure ℚ` which is a curve over it in the sense of `IsCurveOver` (principal divisors, finite residue extensions at every place, and $\Omega_{\bar F/\bar{\mathbb{Q}}}$ free of rank one) and essentially of finite type. Let $\pi_X : X \to \operatorname{Spec} R$ be a scheme over $R$, $\bar s : \operatorname{Spec}\bar{\mathbb{Q}} \to \operatorname{Spec} R$ a morphism, and $\mathrm{pt}$ a rule attaching to every commutative ring $S$, every $S$-point $s$ of $\operatorname{Spec} R$ and every fake elliptic curve $E$ over $S$ (an abelian scheme of relative fibre dimension $2$ with commutative group law, $\Lambda$-action of the prescribed trace type, and level-$N$ structure) a morphism $\operatorname{Spec} S \to X$ over $s$; $\mathrm{pt}$ is assumed invariant under isomorphism of fake elliptic curves, compatible with pullback along ring maps, and, over algebraically closed fields, surjective onto points of $X$ over $s$ and injective up to isomorphism. Let $\mathfrak{M}$ be a `CurveModel` of $\bar F$ over $\bar{\mathbb{Q}}$ (an integral scheme, proper and smooth of relative dimension one over $\bar{\mathbb{Q}}$, with function field identified with $\bar F$ and closed points in bijection with the places), and let $e_{\mathfrak{M}} : \mathfrak{M}.C \to X \times_{\operatorname{Spec} R} \operatorname{Spec}\bar{\mathbb{Q}}$ be an isomorphism whose composite with the second projection is the structure map $\mathfrak{M}.\mathrm{toBase}$. Finally let $\pi_Y : Y \to \operatorname{Spec}\bar{\mathbb{Q}}$ be integral, separated and smooth of relative dimension one, equipped with a rule $\mathrm{pt}_Y$ making $(Y,\pi_Y,\mathrm{pt}_Y)$ satisfy `IsCoarseModuli` for the same $\Lambda$ and $N$ over $\bar{\mathbb{Q}}$, i.e. the four point-laws together with the universal property for all rules into other $\bar{\mathbb{Q}}$-schemes. Then there exists $g : Y \to X \times_{\operatorname{Spec} R} \operatorname{Spec}\bar{\mathbb{Q}}$ which is an isomorphism, satisfies $\pi_Y =$ ($g$ followed by the second projection), and is compatible with the moduli maps: for every commutative ring $S$, every $s : \operatorname{Spec} S \to \operatorname{Spec}\bar{\mathbb{Q}}$ and every fake elliptic curve $E$ over $S$, the composite $\mathrm{pt}_Y(S,s,E)$ followed by $g$ followed by the first projection equals $\mathrm{pt}(S, s \circ \bar s, E)$.
--
--   This is the uniqueness half of the coarse moduli description of a Shimura curve of quaternionic type: any integral separated smooth curve over $\bar{\mathbb{Q}}$ coarsely classifying fake elliptic curves with $\Lambda$-action and level-$N$ structure is identified, compatibly with the classifying maps, with the $\bar{\mathbb{Q}}$-fibre of a given model over $\mathbb{Z}[1/D]$, here known to be the smooth proper model of $\bar F/\bar{\mathbb{Q}}$. It feeds the construction of the moduli tower witness used in the Čerednik–Drinfeld input to the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCoarseModuli_exists_iso_pullback_awayD.lean

import Definitions.Def_CerednikDrinfeld_QMModuliTower
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM AlgebraicCurve NeronModelInfra

theorem CerednikDrinfeld.QM.IsCoarseModuli.exists_iso_pullback_awayD
    {N : ℕ} [NeZero N]
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (D : ℕ)

    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    [IsCurveOver (AlgebraicClosure ℚ) Fbar] [Algebra.EssFiniteType (AlgebraicClosure ℚ) Fbar]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (pt_iso : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (E E' : FakeEllipticCurve Λ N S), FakeEllipticCurve.Iso E E' → pt S s E = pt S s E')
    (pt_pullback : ∀ (S S' : Type) [CommRing S] [CommRing S'] (φ : S →+* S')
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (s' : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      Spec.map (CommRingCat.ofHom φ) ≫ s = s' → ∀ (E : FakeEllipticCurve Λ N S) (E' : FakeEllipticCurve Λ N S'),
      FakeEllipticCurve.IsPullback φ E E' → (pt S' s' E').1 = Spec.map (CommRingCat.ofHom φ) ≫ (pt S s E).1)
    (pt_surjective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (x : SchemeHomOver s πX), ∃ E : FakeEllipticCurve Λ N k, pt k s E = x)
    (pt_injective : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
      (E E' : FakeEllipticCurve Λ N k), pt k s E = pt k s E' → FakeEllipticCurve.Iso E E')

    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar)
    (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar) [CategoryTheory.IsIso e𝔐]
    (he𝔐 : e𝔐 ≫ CategoryTheory.Limits.pullback.snd πX sbar = 𝔐.toBase)

    (Y : Scheme.{0}) (πY : Y ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) [IsIntegral Y] [IsSeparated πY]
    (hYsm : SmoothOfRelativeDimension 1 πY)
    (ptY : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πY)
    (hY : IsCoarseModuli Λ N Y πY ptY) :
    ∃ g : Y ⟶ CategoryTheory.Limits.pullback πX sbar, IsIso g ∧ g ≫ CategoryTheory.Limits.pullback.snd πX sbar = πY ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (E : FakeEllipticCurve Λ N S),
        (ptY S s E).1 ≫ g ≫ CategoryTheory.Limits.pullback.fst πX sbar = (pt S (s ≫ sbar) E).1 := by sorry
