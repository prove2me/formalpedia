-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_rosatiCompatible_of_forall_rosatiCompatible_pullback_of_isPullback_pi
-- name    : AlgebraicGeometry.Polarisation.rosatiCompatible_of_forall_rosatiCompatible_pullback_of_isPullback_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/51ad3ac1-d572-533c-951e-4047605bbb39
-- title:
--   Rosati compatibility descends from the factors of a finite product base
-- statement:
--   Fix $k \in \mathbb{N}$ and commutative rings $C i$ for $i \in \mathrm{Fin}\,k$. Let $A'$ be a scheme with a morphism $f' : A' \to \operatorname{Spec}(\prod_i C i)$, let $L'$ be a relative group law on $f'$ (a functorial group structure on the sets $\{\varphi : T \to A' \mid \varphi \circ f' = t\}$ of points over the base, with multiplication, unit and inverse natural in $T$), and let $\mathcal{L}$ be a module on $A'$ that is invertible, i.e. locally on $A'$ isomorphic to the unit. Let $f_i : A_i \to \operatorname{Spec}(C i)$ and $v_i : A_i \to A'$ be such that each square formed by $v_i$, $f_i$, $f'$ and $\operatorname{Spec}$ of the $i$-th evaluation $\prod_j C j \to C i$ is cartesian, let $L_i$ be a relative group law on $f_i$, and assume each $v_i$ is a homomorphism: for every $T$, every $t : T \to \operatorname{Spec}(C i)$ and all points $P, Q$ over $t$, composing the $L_i$-product of $P$ and $Q$ with $v_i$ gives the $L'$-product of $P \circ v_i$ and $Q \circ v_i$ over $t$ followed by the evaluation. Let $I$ be a type, $\mathrm{act} : I \to \operatorname{End}(A')$ with $\mathrm{act}(x)$ over $f'$, $\mathrm{star} : I \to I$, and $\mathrm{acti}_i : I \to \operatorname{End}(A_i)$ with $\mathrm{acti}_i(x)$ over $f_i$ and $\mathrm{acti}_i(x)$ followed by $v_i$ equal to $v_i$ followed by $\mathrm{act}(x)$. Assume that for each $i$ the datum $(f_i, L_i, v_i^{*}\mathcal{L}, \mathrm{acti}_i, \mathrm{star})$ satisfies `RosatiCompatible`. Then $(f', L', \mathcal{L}, \mathrm{act}, \mathrm{star})$ satisfies `RosatiCompatible`: for every $b \in I$, the two pullbacks of the Mumford bundle $m^{*}\mathcal{L} \otimes (\mathrm{pr}_1^{*}\mathcal{L}^{\vee} \otimes \mathrm{pr}_2^{*}\mathcal{L}^{\vee})$ on $A' \times_{\operatorname{Spec}(\prod_i C i)} A'$ along $(\mathrm{pr}_1, \mathrm{pr}_2 \circ \mathrm{act}(b))$ and along $(\mathrm{pr}_1 \circ \mathrm{act}(\mathrm{star}\,b), \mathrm{pr}_2)$ become isomorphic after restriction to the preimage of some open neighbourhood of each point of the base.
--
--   Spectra of finite products of rings decompose as disjoint unions of the spectra of the factors, and the Rosati condition relating an action on an abelian scheme to the Mumford bundle of a polarisation is a condition that is local on the base; this lemma assembles the condition over $\operatorname{Spec}(\prod_i C i)$ from the conditions over the factors $\operatorname{Spec}(C i)$. It is used in the construction of canonical polarisation data for fake elliptic curves in the Čerednik–Drinfel'd part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_rosatiCompatible_of_forall_rosatiCompatible_pullback_of_isPullback_pi.lean

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

theorem AlgebraicGeometry.Polarisation.rosatiCompatible_of_forall_rosatiCompatible_pullback_of_isPullback_pi
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
    {I : Type} (act : I → (A' ⟶ A')) (act_over : ∀ x : I, act x ≫ f' = f') (star : I → I)
    (acti : ∀ i, I → (Ai i ⟶ Ai i)) (acti_over : ∀ (i : Fin k) (x : I), acti i x ≫ fi i = fi i)
    (hact : ∀ (i : Fin k) (x : I), acti i x ≫ v i = v i ≫ act x)
    (h : ∀ i, RosatiCompatible (fi i) (Li i) ((Scheme.Modules.pullback (v i)).obj 𝓛) (acti i) (acti_over i) star) :
    RosatiCompatible f' L' 𝓛 act act_over star := by sorry
