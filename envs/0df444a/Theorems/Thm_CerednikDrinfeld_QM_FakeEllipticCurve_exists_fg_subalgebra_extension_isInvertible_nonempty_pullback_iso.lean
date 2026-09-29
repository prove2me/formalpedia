-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_extension_isInvertible_nonempty_pullback_iso
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_extension_isInvertible_nonempty_pullback_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/13641a99-cd2b-50a2-9935-6866080db33e
-- title:
--   Invertible module descends to an enlarged finitely generated stage
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ which is a maximal order (an order, and maximal among orders containing it), a natural number $N$, and a commutative ring $R$. Let $E$ be a fake elliptic curve over $R$ in the sense of the project structure `FakeEllipticCurve` (a scheme $E.A$ over $\operatorname{Spec} R$ with a commutative relative group law, the abelian-scheme property bundle, fibres of dimension $2$, an action of $\Lambda$ by endomorphisms over the base, and the level-$N$ data). Let $T_0$ be a finitely generated $\mathbb{Z}$-subalgebra of $R$, let $E_0$ be a fake elliptic curve over $T_0$, and let $g_0 : E.A \to E_0.A$ be a morphism making the square over $\operatorname{Spec}(T_0 \hookrightarrow R)$ cartesian, compatible with the two group laws on points over arbitrary $R$-schemes, and $\Lambda$-equivariant. Let $\mathcal{M}$ be a module on $E.A$ which is invertible, i.e. every point has an open neighbourhood $U$ with the restriction of $\mathcal{M}$ to $U$ isomorphic to the unit sheaf. The assertion is that there exist a finitely generated $\mathbb{Z}$-subalgebra $T$ of $R$ with $T_0 \le T$, a fake elliptic curve $E_T$ over $T$, and morphisms $g : E.A \to E_T.A$ and $h : E_T.A \to E_0.A$ such that both induced squares (over $\operatorname{Spec}(T \hookrightarrow R)$ and over $\operatorname{Spec}(T_0 \hookrightarrow T)$) are cartesian, $g$ followed by $h$ equals $g_0$, both $g$ and $h$ are compatible with the group laws on points and $\Lambda$-equivariant, and there is an invertible module $\mathcal{M}_T$ on $E_T.A$ whose pullback along $g$ is isomorphic to $\mathcal{M}$. Note that the compatibility obtained for $g$ and $h$ is that of a cartesian, group-law- and $\Lambda$-compatible morphism only; the level-structure clause of the project's relation `FakeEllipticCurve.IsPullback` (factorisation of points through the level covering) is not part of the conclusion.
--
--   This is a spreading-out step of the standard limit kind: an invertible sheaf on a fake elliptic curve over $R$ already lives over a finitely generated subring, which may moreover be taken to contain a prescribed finitely generated stage. It feeds the descent of a fake elliptic curve together with its two-torsion and polarisation data to a finitely generated base, used in the Čerednik–Drinfel'd part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_extension_isInvertible_nonempty_pullback_iso.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_extension_isInvertible_nonempty_pullback_iso
    {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (N : ℕ) (R : Type) [CommRing R] (E : FakeEllipticCurve Λ N R)
    (T₀ : Subalgebra ℤ R) (hT₀ : T₀.FG) (E₀ : FakeEllipticCurve Λ N ↥T₀) (g₀ : E.A ⟶ E₀.A)
    (hg₀ : CategoryTheory.IsPullback g₀ E.f E₀.f (Spec.map (CommRingCat.ofHom T₀.val.toRingHom)))
    (hlaw₀ :
      (∀ {X : Scheme.{0}} (t' : X ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ g₀ =
          (E₀.L.mul (t' ≫ Spec.map (CommRingCat.ofHom T₀.val.toRingHom))
            ⟨P.1 ≫ g₀, by rw [Category.assoc, hg₀.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g₀, by rw [Category.assoc, hg₀.w, ← Category.assoc, Q.2]⟩).1))
    (hact₀ : ∀ x : ↥Λ, E.act x ≫ g₀ = g₀ ≫ E₀.act x)
    (𝓜 : E.A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) :
    ∃ (T : Subalgebra ℤ R) (_ : T.FG) (hle : T₀ ≤ T) (ET : FakeEllipticCurve Λ N ↥T) (g : E.A ⟶ ET.A)
      (hg : CategoryTheory.IsPullback g E.f ET.f (Spec.map (CommRingCat.ofHom T.val.toRingHom)))
      (h : ET.A ⟶ E₀.A)
      (hh : CategoryTheory.IsPullback h ET.f E₀.f (Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom))),
      g ≫ h = g₀ ∧
      (∀ {X : Scheme.{0}} (t' : X ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t' E.f),
        (E.L.mul t' P Q).1 ≫ g =
          (ET.L.mul (t' ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom))
            ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, E.act x ≫ g = g ≫ ET.act x) ∧
      (∀ {X : Scheme.{0}} (t' : X ⟶ Spec (CommRingCat.of ↥T)) (P Q : SchemeHomOver t' ET.f),
        (ET.L.mul t' P Q).1 ≫ h =
          (E₀.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (Subalgebra.inclusion hle).toRingHom))
            ⟨P.1 ≫ h, by rw [Category.assoc, hh.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ h, by rw [Category.assoc, hh.w, ← Category.assoc, Q.2]⟩).1) ∧
      (∀ x : ↥Λ, ET.act x ≫ h = h ≫ E₀.act x) ∧
      ∃ 𝓜T : ET.A.Modules, Scheme.Modules.IsInvertible 𝓜T ∧ Nonempty ((Scheme.Modules.pullback g).obj 𝓜T ≅ 𝓜) := by sorry
