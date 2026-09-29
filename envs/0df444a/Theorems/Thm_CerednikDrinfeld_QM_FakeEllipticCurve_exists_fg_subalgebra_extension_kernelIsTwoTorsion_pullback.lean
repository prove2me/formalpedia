-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_extension_kernelIsTwoTorsion_pullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_extension_kernelIsTwoTorsion_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/93067c08-4190-5e65-ab40-104c316fa709
-- title:
--   Spreading K(M)=E[2] to a finitely generated stage
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ which is an order maximal among orders (`IsMaximalOrder`), a natural number $N$, a commutative ring $R$ and a fake elliptic curve $E$ of type $(\Lambda,N)$ over $R$: a scheme $E.A$ with a structure morphism $E.f$ to $\operatorname{Spec} R$, a commutative relative group law $E.L$ on its functor of points, an abelian-scheme property bundle, fibres of dimension $2$, a $\Lambda$-action $E.\mathrm{act}$ by endomorphisms over the base compatible with the group law and with the trace condition, and level data. Assume given a finitely generated $\mathbb{Z}$-subalgebra $T_0 \subseteq R$, a fake elliptic curve $E_0$ of the same type over $T_0$, and a morphism $g_0 : E.A \to E_0.A$ making the square over $\operatorname{Spec} T_0 \leftarrow \operatorname{Spec} R$ cartesian, such that $g_0$ is compatible with the group laws on $T$-valued points for every base scheme and test morphism $t'$ to $\operatorname{Spec} R$, and satisfies $E.\mathrm{act}(x)$ followed by $g_0$ equals $g_0$ followed by $E_0.\mathrm{act}(x)$ for all $x \in \Lambda$. Let $\mathcal{M}_0$ be a module on $E_0.A$ which is invertible (locally isomorphic to the unit module), and assume `KernelIsTwoTorsion` holds for $E.f$, $E.L$ and $g_0^{*}\mathcal{M}_0$: for every commutative ring $R'$, every $t : \operatorname{Spec} R' \to \operatorname{Spec} R$ and every section $x$ of $E.f$ over $t$, the pullback along $\mathrm{sliceAt}(x)$ of the Mumford bundle of $g_0^{*}\mathcal{M}_0$ is locally isomorphic on the base to the unit module precisely when $x$ is $2$-torsion for $E.L$. Then there exist a finitely generated $\mathbb{Z}$-subalgebra $T$ of $R$ with $T_0 \le T$, a fake elliptic curve $E_T$ of type $(\Lambda,N)$ over $T$, and morphisms $g : E.A \to E_T.A$ and $h : E_T.A \to E_0.A$ whose squares over $\operatorname{Spec} T \leftarrow \operatorname{Spec} R$ and $\operatorname{Spec} T_0 \leftarrow \operatorname{Spec} T$ are cartesian, such that $g$ followed by $h$ is $g_0$, both $g$ and $h$ are compatible with the group laws on points over arbitrary test bases and with the $\Lambda$-actions, and `KernelIsTwoTorsion` holds for $E_T.f$, $E_T.L$ and $h^{*}\mathcal{M}_0$.
--
--   This is the spreading-out step which descends the condition that the kernel of the Mumford bundle of an invertible module equals the full $2$-torsion from the ring $R$ to a finitely generated stage, after enlarging that stage; the two factorisations $g$, $h$ keep track of the compatible fake elliptic curve over the larger subalgebra. It feeds the construction of a finitely generated stage carrying both a trivial-kernel polarisation datum and an isomorphism identifying its pullback, used in the moduli-theoretic part of the Čerednik–Drinfeld development of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_extension_kernelIsTwoTorsion_pullback.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_extension_kernelIsTwoTorsion_pullback
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
    (𝓜₀ : E₀.A.Modules) (h₀ : Scheme.Modules.IsInvertible 𝓜₀)
    (hK : KernelIsTwoTorsion E.f E.L ((Scheme.Modules.pullback g₀).obj 𝓜₀)) :
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
      KernelIsTwoTorsion ET.f ET.L ((Scheme.Modules.pullback h).obj 𝓜₀) := by sorry
