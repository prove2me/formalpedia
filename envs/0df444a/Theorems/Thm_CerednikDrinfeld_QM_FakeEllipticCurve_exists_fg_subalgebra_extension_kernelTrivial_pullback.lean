-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_extension_kernelTrivial_pullback
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_extension_kernelTrivial_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:05.481085+00:00
-- url     : https://prove2.me/theorems/10416a2e-7d01-5b9b-addb-3a20978492c1
-- title:
--   Triviality of the Mumford kernel over a finitely generated stage
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ which is a maximal order (an order contained in no strictly larger order), a natural number $N$, a commutative ring $R$, and a fake elliptic curve $E$ of level data $(\Lambda,N)$ over $R$. Suppose given a finitely generated $\mathbb{Z}$-subalgebra $T_0 \subseteq R$, a fake elliptic curve $E_0$ over $T_0$, and a morphism $g_0 : E.A \to E_0.A$ making the square over $\operatorname{Spec} R \to \operatorname{Spec} T_0$ a pullback, i.e. exhibiting $E.A$ as the base change of $E_0.A$; assume moreover that $g_0$ is compatible with the relative group laws on points (for every scheme $X$, every $t' : X \to \operatorname{Spec} R$ and all $t'$-points $P,Q$ of $E.f$, the product $P\cdot Q$ followed by $g_0$ is the product of $P \circ g_0$ and $Q \circ g_0$ over $t'$ followed by $\operatorname{Spec} R \to \operatorname{Spec} T_0$) and that $E.\mathrm{act}\,x$ followed by $g_0$ equals $g_0$ followed by $E_0.\mathrm{act}\,x$ for every $x \in \Lambda$. Let $\mathcal{M}_0$ be an invertible module on $E_0.A$ (locally on $E_0.A$ isomorphic to the unit) and assume `KernelTrivial` for $E.f$, $E.L$ and $g_0^{*}\mathcal{M}_0$: for every commutative ring $R'$, every $t : \operatorname{Spec} R' \to \operatorname{Spec} R$ and every $t$-point $x$ of $E.f$, if the pullback along $\mathrm{sliceAt}(x)$ of the Mumford bundle $m^{*}\mathcal{L} \otimes \mathrm{pr}_1^{*}\mathcal{L}^{\vee} \otimes \mathrm{pr}_2^{*}\mathcal{L}^{\vee}$ of $\mathcal{L} = g_0^{*}\mathcal{M}_0$ is, locally on the base, isomorphic to the unit object, then $x$ is the unit section over $t$. The conclusion asserts the existence of a finitely generated $\mathbb{Z}$-subalgebra $T \subseteq R$ with $T_0 \le T$, a fake elliptic curve $E_T$ of level data $(\Lambda,N)$ over $T$, and morphisms $g : E.A \to E_T.A$ and $h : E_T.A \to E_0.A$ which are pullback squares over $\operatorname{Spec} R \to \operatorname{Spec} T$ and over the map induced by $T_0 \hookrightarrow T$ respectively, such that $g$ followed by $h$ is $g_0$, both $g$ and $h$ are compatible with the relative group laws on points in the above sense and satisfy the corresponding $\Lambda$-equivariance relations, and `KernelTrivial` holds for $E_T.f$, $E_T.L$ and $h^{*}\mathcal{M}_0$.
--
--   This is the spreading-out step which, for a fake elliptic curve written as a limit of finitely generated stages, moves the condition that the Mumford kernel $K(\mathcal{M})$ is reduced to the unit section from the limit down to a finitely generated base, after enlarging the stage. It feeds the combined statement assembling an invertible module together with the two-torsion kernel and kernel-triviality conditions at a single finitely generated stage.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_fg_subalgebra_extension_kernelTrivial_pullback.lean

import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_fg_subalgebra_extension_kernelTrivial_pullback
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
    (hK : KernelTrivial E.f E.L ((Scheme.Modules.pullback g₀).obj 𝓜₀)) :
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
      KernelTrivial ET.f ET.L ((Scheme.Modules.pullback h).obj 𝓜₀) := by sorry
