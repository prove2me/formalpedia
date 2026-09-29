-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_isPullback_of_descent_of_faithfullyFlat
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_isPullback_of_descent_of_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/e83d9942-95c1-5b38-ba3e-423726cfb926
-- title:
--   Descent of polarised abelian scheme structure along faithfully flat base change
-- statement:
--   Fix natural numbers $g$, $d$, $n$ and a commutative ring $S$, and let $S'$ be a commutative $S$-algebra that is faithfully flat as an $S$-module. The data are: a polarised abelian scheme $u'$ of invariants $(g,d,n)$ over $S'$ — that is, a scheme $u'.A$ with a structure morphism to $\operatorname{Spec} S'$, a commutative relative group law $u'.L$ on its functor of points, smoothness, properness, connected fibres and existence of a group law, all fibres of topological Krull dimension $g$, sections $u'.P_i$ ($i < 2g$) killed by $n$ which are independent and span the $n$-torsion at every algebraically closed geometric point, and an invertible module $u'.\mathrm{pol}$ admitting a projective presentation over the base whose associated morphism to projective space is a closed immersion, with geometric fibrewise $H^0$-rank $d$ — together with a polarised abelian scheme $v''$ of the same invariants over $S' \otimes_S S'$ and two morphisms $a_1, a_2 : v''.A \to u'.A$ whose squares over $\operatorname{Spec}$ of the left and right inclusions $S' \to S' \otimes_S S'$ are pullbacks, each compatible with the group laws on $T$-points and carrying the level sections of $v''$ to the corresponding base changes of those of $u'$. Further data: a scheme $X$ with a morphism $f : X \to \operatorname{Spec} S$ and a morphism $c : u'.A \to X$ making $u'.A$ the pullback of $X$ along $\operatorname{Spec}$ of $S \to S'$, satisfying $a_1$ followed by $c$ equals $a_2$ followed by $c$, and a module $L$ on $X$ that is invertible, admits a projective presentation over $f$ with closed-immersion associated morphism, and whose pullback along $c$ is isomorphic to $u'.\mathrm{pol}$. The conclusion is the existence of a polarised abelian scheme $u$ of invariants $(g,d,n)$ over $S$ with $u.A = X$ such that $u'$ is the base change of $u$ along $S \to S'$ in the structured sense: some $g_A : u'.A \to u.A$ makes a pullback square over $\operatorname{Spec}$ of $S \to S'$, is compatible with the two group laws on $T$-points, carries the sections $u'.P_i$ to the base changes of $u.P_i$, and pulls $u.\mathrm{pol}$ back to a module isomorphic to $u'.\mathrm{pol}$. Note that the conclusion asserts only the equality $u.A = X$ of underlying schemes; it does not assert that $u.f$ is $f$ or that $u.\mathrm{pol}$ is $L$.
--
--   This is the fpqc descent step for the whole package of structure carried by a polarised abelian scheme: once the total space and the polarisation have been descended along a faithfully flat base change, the group law, the level structure and the numerical invariants descend with them. It is used by [`AlgebraicGeometry.PolarisedAbelianScheme.exists_descent_and_iso_of_faithfullyFlat_of_three_le_of_rigidified`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_descent_and_iso_of_faithfullyFlat_of_three_le_of_rigidified).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_isPullback_of_descent_of_faithfullyFlat.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_isPullback_of_descent_of_faithfullyFlat
    {g d n : ℕ} {S : Type} [CommRing S]
    (S' : Type) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    (u' : PolarisedAbelianScheme g d n S')
    (v'' : PolarisedAbelianScheme g d n (S' ⊗[S] S')) (a₁ a₂ : v''.A ⟶ u'.A)
    (ha₁ : CategoryTheory.IsPullback a₁ v''.f u'.f (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (ha₂ : CategoryTheory.IsPullback a₂ v''.f u'.f (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (ha₁mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (x y : SchemeHomOver t' v''.f),
      (v''.L.mul t' x y).1 ≫ a₁ =
        (u'.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom))
          ⟨x.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, y.2]⟩).1)
    (ha₂mul : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (x y : SchemeHomOver t' v''.f),
      (v''.L.mul t' x y).1 ≫ a₂ =
        (u'.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom))
          ⟨x.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, y.2]⟩).1)
    (ha₁P : ∀ i, (v''.P i).1 ≫ a₁ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom) ≫ (u'.P i).1)
    (ha₂P : ∀ i, (v''.P i).1 ≫ a₂ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom) ≫ (u'.P i).1)

    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of S)) (c : u'.A ⟶ X)
    (hc : CategoryTheory.IsPullback c u'.f f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (hca : a₁ ≫ c = a₂ ≫ c)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (hLva : Scheme.Modules.ClosedImmersionBySections L f)
    (hcL : Nonempty ((Scheme.Modules.pullback c).obj L ≅ u'.pol)) :
    ∃ u : PolarisedAbelianScheme g d n S, ∃ (hA : u.A = X), PolarisedAbelianScheme.IsPullback (algebraMap S S') u u' := by sorry
