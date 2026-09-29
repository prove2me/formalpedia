-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_of_forall_kernelIsTwoTorsion_pullback_of_isPullback_pi
-- name    : AlgebraicGeometry.Polarisation.kernelIsTwoTorsion_of_forall_kernelIsTwoTorsion_pullback_of_isPullback_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/a1f6725a-5783-5c14-9459-1518d50b006a
-- title:
--   Two-torsion kernel condition over a finite product base
-- statement:
--   Let $k$ be a natural number and $C : \mathrm{Fin}\,k \to \mathrm{Type}$ a family of commutative rings, and put $S = \prod_i C_i$. Let $f' : A' \to \operatorname{Spec} S$ be a morphism of schemes carrying a relative group law $L'$, i.e. for each $t : T \to \operatorname{Spec} S$ a group structure (multiplication, unit, inverse, with associativity, unit and inverse laws) on the sections $\{\varphi : T \to A' \mid \varphi \circ f' = t\}$, natural in base change along $T' \to T$. Let $\mathcal L$ be a module on $A'$ that is invertible, in the sense that every point of $A'$ has an open neighbourhood on which $\mathcal L$ restricts to a module isomorphic to the unit. Let $f_i : A_i \to \operatorname{Spec} C_i$ be morphisms with relative group laws $L_i$, and let $v_i : A_i \to A'$ be morphisms such that each square formed by $v_i$, $f_i$, $f'$ and $\operatorname{Spec}$ of the $i$-th projection $S \to C_i$ is a pullback, and such that each $v_i$ is a homomorphism: for every $t : T \to \operatorname{Spec} C_i$ and sections $P, Q$ of $f_i$ over $t$, the morphism underlying $L_i$-product of $P$ and $Q$ followed by $v_i$ agrees with the morphism underlying the $L'$-product, over $t$ followed by $\operatorname{Spec}$ of the projection, of $P$ followed by $v_i$ and $Q$ followed by $v_i$. Assume for each $i$ that `KernelIsTwoTorsion` holds for $f_i$, $L_i$ and the pullback of $\mathcal L$ along $v_i$: for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} C_i$ and every section $x$ of $f_i$ over $t$, the pullback along the slice morphism $\mathrm{sliceAt}$ at $x$ of the Mumford bundle $\mathrm{add}^*\mathcal M \otimes (\mathrm{pr}_1^*\mathcal M^\vee \otimes \mathrm{pr}_2^*\mathcal M^\vee)$ (for $\mathcal M = v_i^*\mathcal L$) is locally isomorphic to the unit module over the base, i.e. every point of $\operatorname{Spec} C_i$ has an open neighbourhood $U$ whose preimage under the second projection $\operatorname{Spec} R \times_{\operatorname{Spec} C_i} A_i \to \operatorname{Spec} R$ carries an isomorphism between the two restricted modules, if and only if the $L_i$-square of $x$ is the unit section. Then the same statement `KernelIsTwoTorsion` holds for $f'$, $L'$ and $\mathcal L$.
--
--   This is the assertion that the condition $K(\mathcal L) = A[2]$, expressed through local triviality of the slices of the Mumford bundle, is detected componentwise when the base is a finite product of rings, so that $\operatorname{Spec} S$ is the disjoint union of the $\operatorname{Spec} C_i$. It is used in the construction of canonical polarisation data on a product of fake elliptic curves in the Cherednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_kernelIsTwoTorsion_of_forall_kernelIsTwoTorsion_pullback_of_isPullback_pi.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.kernelIsTwoTorsion_of_forall_kernelIsTwoTorsion_pullback_of_isPullback_pi
    {k : ℕ} (C : Fin k → Type) [∀ i, CommRing (C i)]
    {A' : Scheme.{0}} (f' : A' ⟶ Spec (CommRingCat.of (∀ i, C i))) (L' : RelativeGroupLaw (∀ i, C i) f')
    (𝓛 : A'.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    {Ai : Fin k → Scheme.{0}} (fi : ∀ i, Ai i ⟶ Spec (CommRingCat.of (C i))) (v : ∀ i, Ai i ⟶ A')
    (hv : ∀ i, IsPullback (v i) (fi i) f' (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))))
    (Li : ∀ i, RelativeGroupLaw (C i) (fi i))
    (hLi : ∀ (i : Fin k) (T : Scheme.{0}) (t : T ⟶ Spec (CommRingCat.of (C i))) (P Q : SchemeHomOver t (fi i)),
      ((Li i).mul t P Q).1 ≫ v i =
        (L'.mul (t ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i)))
          ⟨P.1 ≫ v i, by rw [Category.assoc, (hv i).w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ v i, by rw [Category.assoc, (hv i).w, ← Category.assoc, Q.2]⟩).1)
    (h : ∀ i, KernelIsTwoTorsion (fi i) (Li i) ((Scheme.Modules.pullback (v i)).obj 𝓛)) :
    KernelIsTwoTorsion f' L' 𝓛 := by sorry
