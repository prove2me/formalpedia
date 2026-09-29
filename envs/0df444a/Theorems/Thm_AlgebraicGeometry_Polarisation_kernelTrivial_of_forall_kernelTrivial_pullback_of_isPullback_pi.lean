-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_kernelTrivial_of_forall_kernelTrivial_pullback_of_isPullback_pi
-- name    : AlgebraicGeometry.Polarisation.kernelTrivial_of_forall_kernelTrivial_pullback_of_isPullback_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/cd698da8-1315-5a0f-8df6-a5e7afd7f2e7
-- title:
--   Kernel triviality descends from the factors of a product base
-- statement:
--   Fix $k \in \mathbb{N}$ and commutative rings $C_i$ for $i \in \mathrm{Fin}\,k$. Let $f' : A' \to \operatorname{Spec}\bigl(\prod_i C_i\bigr)$ be a morphism of schemes equipped with a relative group law $L'$, that is, a functorial multiplication, unit and inverse on the sets $\{\varphi : T \to A' \mid \varphi \circ f' = t\}$ of $A'$-points over arbitrary test morphisms $t : T \to \operatorname{Spec}(\prod_i C_i)$, satisfying associativity, the unit and inverse laws and compatibility with base change along $T' \to T$. Let $\mathcal{L}$ be a module on $A'$ which is invertible in the sense that every point of $A'$ has an open neighbourhood $U$ on which the restriction of $\mathcal{L}$ is isomorphic to the unit sheaf of modules. Suppose given schemes $A_i$ with structure morphisms $f_i : A_i \to \operatorname{Spec} C_i$, morphisms $v_i : A_i \to A'$ such that each square formed by $v_i$, $f_i$, $f'$ and $\operatorname{Spec}$ of the $i$-th projection $\prod_j C_j \to C_i$ is cartesian, and relative group laws $L_i$ on $f_i$ for which each $v_i$ is a homomorphism on points: for every test morphism $t : T \to \operatorname{Spec} C_i$ and all $P, Q$ in $A_i(T)$ over $t$, the point $L_i.\mathrm{mul}(t,P,Q)$ followed by $v_i$ equals $L'.\mathrm{mul}$ applied, over $t$ followed by $\operatorname{Spec}$ of the $i$-th projection, to $P$ followed by $v_i$ and $Q$ followed by $v_i$. Assume finally that for each $i$ the predicate `KernelTrivial` holds for $f_i$, $L_i$ and the pullback of $\mathcal{L}$ along $v_i$, i.e. for every commutative ring $R$, every $t : \operatorname{Spec} R \to \operatorname{Spec} C_i$ and every point $x$ of $A_i$ over $t$, if the pullback along the slice $\mathrm{sliceAt}(x)$ of the Mumford bundle $m^*v_i^*\mathcal{L} \otimes \mathrm{pr}_1^*(v_i^*\mathcal{L})^{\vee} \otimes \mathrm{pr}_2^*(v_i^*\mathcal{L})^{\vee}$ on $A_i \times_{\operatorname{Spec} C_i} A_i$ is, locally on the base $\operatorname{Spec} R$, isomorphic to the unit object, then $x$ is the unit point $L_i.\mathrm{one}(t)$. The conclusion is that the same condition `KernelTrivial` holds for $f'$, $L'$ and $\mathcal{L}$.
--
--   This is the statement that the condition $K(\mathcal{L}) = e$, formulated via local triviality of the Mumford bundle restricted to the slice through a point, may be checked after base change to the factors of a finite product of rings, the base $\operatorname{Spec}(\prod_i C_i)$ being the disjoint union of the $\operatorname{Spec} C_i$. It is used in the construction of a faithfully flat base change carrying a principal square root of a polarisation over such a product base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_kernelTrivial_of_forall_kernelTrivial_pullback_of_isPullback_pi.lean

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

theorem AlgebraicGeometry.Polarisation.kernelTrivial_of_forall_kernelTrivial_pullback_of_isPullback_pi
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
    (h : ∀ i, KernelTrivial (fi i) (Li i) ((Scheme.Modules.pullback (v i)).obj 𝓛)) :
    KernelTrivial f' L' 𝓛 := by sorry
