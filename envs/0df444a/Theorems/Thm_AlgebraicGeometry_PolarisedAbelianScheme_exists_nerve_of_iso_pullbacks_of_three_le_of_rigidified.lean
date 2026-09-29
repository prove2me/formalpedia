-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_nerve_of_iso_pullbacks_of_three_le_of_rigidified
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.exists_nerve_of_iso_pullbacks_of_three_le_of_rigidified
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/ee7048c4-a57f-5dab-9c40-b00110e75ea8
-- title:
--   Rigidity yields a nerve datum for polarised abelian schemes
-- statement:
--   Fix natural numbers $g,d,n$ with $3\le n$, a commutative ring $S$ in which the image of $n$ is a unit, and a commutative $S$-algebra $S'$ that is faithfully flat as an $S$-module. Let $u'$ be a polarised abelian scheme of type $(g,d,n)$ over $S'$ in the sense of the project structure: a scheme $u'.A$ with a structure morphism $u'.f$ to $\operatorname{Spec} S'$, a commutative relative group law $u'.L$ on its functor of points, an `AbelianSchemePropertyBundle`, fibres of topological Krull dimension $g$, $2g$ sections $u'.P i$ that are $n$-torsion and form a basis of the $n$-torsion on geometric fibres, and an invertible module $u'.pol$ which is a closed immersion by sections over the base and has geometric fibre $H^0$-rank $d$. Assume the rigidification hypothesis that the pullback of $u'.pol$ along the unit section $(u'.L.one(\mathbf 1)).1$ is isomorphic to the unit module on $\operatorname{Spec} S'$, and the descent hypothesis that any two polarised abelian schemes $v_1,v_2$ of type $(g,d,n)$ over $S'\otimes_S S'$ which are pullbacks of $u'$ along $\mathrm{includeLeft}$ and along $\mathrm{includeRight}$ respectively satisfy `PolarisedAbelianScheme.Iso` $v_1\,v_2$ (an isomorphism of the underlying schemes over the base, compatible with the group laws and with the sections $P i$, and carrying one polarisation to the other locally on the base). The conclusion asserts the existence of: a polarised abelian scheme $v''$ of type $(g,d,n)$ over $S'\otimes_S S'$ together with two morphisms $a_1,a_2:v''.A\to u'.A$, each making a cartesian square with $v''.f$, $u'.f$ and $\operatorname{Spec}$ of the corresponding coface $\mathrm{includeLeft}$, resp. $\mathrm{includeRight}$; and a polarised abelian scheme $v'''$ of type $(g,d,n)$ over $S'\otimes_S(S'\otimes_S S')$ with three morphisms $b_{12},b_{13},b_{23}:v'''.A\to v''.A$ making cartesian squares over $\operatorname{Spec}$ of the three cofaces $\mathrm{id}\otimes\mathrm{includeLeft}$, $\mathrm{id}\otimes\mathrm{includeRight}$ and $\mathrm{includeRight}:S'\otimes_S S'\to S'\otimes_S(S'\otimes_S S')$; such that, moreover, each of $a_1$ and $a_2$ is a homomorphism for the group laws, in the sense that for every scheme $T$, every $t':T\to\operatorname{Spec}(S'\otimes_S S')$ and all $T$-points $x,y$ of $v''.f$ over $t'$, the product $v''.L.mul\,t'\,x\,y$ followed by $a_j$ equals the product in $u'$ of $x$ followed by $a_j$ and $y$ followed by $a_j$, taken over $t'$ followed by $\operatorname{Spec}$ of the relevant coface; each $a_j$ carries the level structure, $(v''.P i).1$ followed by $a_j$ being $\operatorname{Spec}$ of the coface followed by $(u'.P i).1$, for all $i$; the nerve identities $b_{12}\!\gg\!a_1=b_{13}\!\gg\!a_1$, $b_{12}\!\gg\!a_2=b_{23}\!\gg\!a_1$, $b_{13}\!\gg\!a_2=b_{23}\!\gg\!a_2$ hold (composition in diagrammatic order); and the two pullbacks $a_1^*u'.pol$ and $a_2^*u'.pol$ are isomorphic globally over $v''.A$. No group-law or level compatibility is asserted for $b_{12},b_{13},b_{23}$ beyond their being cartesian over the cofaces.
--
--   This is the rigidity step which upgrades the mere existence of an isomorphism between the two base changes of $u'$ to $S'\otimes_S S'$ into a descent (Čech cocycle) datum on the nerve of the covering $\operatorname{Spec} S'\to\operatorname{Spec} S$, including the global comparison of the two pullbacks of the polarisation under the rigidification hypothesis. It feeds the faithfully flat descent statement [`AlgebraicGeometry.PolarisedAbelianScheme.exists_descent_and_iso_of_faithfullyFlat_of_three_le_of_rigidified`](thm.html#AlgebraicGeometry.PolarisedAbelianScheme.exists_descent_and_iso_of_faithfullyFlat_of_three_le_of_rigidified), used in the construction of moduli of polarised abelian schemes with level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_exists_nerve_of_iso_pullbacks_of_three_le_of_rigidified.lean

import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

theorem AlgebraicGeometry.PolarisedAbelianScheme.exists_nerve_of_iso_pullbacks_of_three_le_of_rigidified
    {g d n : ℕ} (hn : 3 ≤ n) {S : Type} [CommRing S] (hn' : IsUnit ((n : ℕ) : S))
    (S' : Type) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    (u' : PolarisedAbelianScheme g d n S')

    (hrig : Nonempty ((Scheme.Modules.pullback (u'.L.one (𝟙 _)).1).obj u'.pol ≅ SheafOfModules.unit (Spec (CommRingCat.of S')).ringCatSheaf))
    (hdesc : ∀ (v₁ v₂ : PolarisedAbelianScheme g d n (S' ⊗[S] S')),
      PolarisedAbelianScheme.IsPullback (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom u' v₁ →
      PolarisedAbelianScheme.IsPullback (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom u' v₂ →
      PolarisedAbelianScheme.Iso v₁ v₂) :
    ∃ (v'' : PolarisedAbelianScheme g d n (S' ⊗[S] S')) (a₁ a₂ : v''.A ⟶ u'.A)
      (ha₁ : CategoryTheory.IsPullback a₁ v''.f u'.f (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
      (ha₂ : CategoryTheory.IsPullback a₂ v''.f u'.f (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
      (v''' : PolarisedAbelianScheme g d n (S' ⊗[S] (S' ⊗[S] S'))) (b₁₂ b₁₃ b₂₃ : v'''.A ⟶ v''.A)
      (_ : CategoryTheory.IsPullback b₁₂ v'''.f v''.f (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')).toRingHom)))
      (_ : CategoryTheory.IsPullback b₁₃ v'''.f v''.f (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id S S') (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S')).toRingHom)))
      (_ : CategoryTheory.IsPullback b₂₃ v'''.f v''.f (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' ⊗[S] S' →ₐ[S] S' ⊗[S] (S' ⊗[S] S')).toRingHom))),

      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (x y : SchemeHomOver t' v''.f),
        (v''.L.mul t' x y).1 ≫ a₁ =
          (u'.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom))
            ⟨x.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ a₁, by rw [Category.assoc, ha₁.w, ← Category.assoc, y.2]⟩).1) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (x y : SchemeHomOver t' v''.f),
        (v''.L.mul t' x y).1 ≫ a₂ =
          (u'.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom))
            ⟨x.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, x.2]⟩
            ⟨y.1 ≫ a₂, by rw [Category.assoc, ha₂.w, ← Category.assoc, y.2]⟩).1) ∧

      (∀ i, (v''.P i).1 ≫ a₁ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom) ≫ (u'.P i).1) ∧
      (∀ i, (v''.P i).1 ≫ a₂ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom) ≫ (u'.P i).1) ∧

      b₁₂ ≫ a₁ = b₁₃ ≫ a₁ ∧ b₁₂ ≫ a₂ = b₂₃ ≫ a₁ ∧ b₁₃ ≫ a₂ = b₂₃ ≫ a₂ ∧

      Nonempty ((Scheme.Modules.pullback a₁).obj u'.pol ≅ (Scheme.Modules.pullback a₂).obj u'.pol) := by sorry
