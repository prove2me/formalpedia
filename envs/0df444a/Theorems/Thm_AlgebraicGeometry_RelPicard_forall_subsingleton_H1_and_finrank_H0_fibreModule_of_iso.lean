-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelPicard_forall_subsingleton_H1_and_finrank_H0_fibreModule_of_iso
-- name    : AlgebraicGeometry.RelPicard.forall_subsingleton_H1_and_finrank_H0_fibreModule_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:46.544029+00:00
-- url     : https://prove2.me/theorems/88ac5e9f-38f6-5210-af76-6b8ef866239a
-- title:
--   Fibrewise Čech conditions transfer along an isomorphism of modules
-- statement:
--   Let $R$ be a commutative ring, let $C$ and $T$ be schemes with morphisms $c \colon C \to \operatorname{Spec} R$ and $t \colon T \to \operatorname{Spec} R$, let $F$ and $F'$ be $\mathcal{O}$-modules on the fibre product $C \times_{\operatorname{Spec} R} T$, let $e \colon F \cong F'$ be an isomorphism of such modules, and let $n$ be a natural number. Assume that for every field $k$, every morphism $s \colon \operatorname{Spec} k \to T$ and every two-affine open cover $\mathcal{W}$ of the fibre $X_s := (C \times_R T) \times_T \operatorname{Spec} k$ — that is, a pair of affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine — the following hold for the pullback $\mathcal{F}_s$ of $F$ along the first projection $X_s \to C \times_R T$, cohomology being computed from the two-term complex $\Gamma(\mathcal{F}_s, U_0) \times \Gamma(\mathcal{F}_s, U_1) \to \Gamma(\mathcal{F}_s, U_0 \sqcap U_1)$, $(m_0,m_1) \mapsto m_1|_{U_0 \cap U_1} - m_0|_{U_0 \cap U_1}$, taken $k$-linearly via the structure morphism $X_s \to \operatorname{Spec} k$: its cokernel $H^1$ is a subsingleton, and its kernel $H^0$ has $k$-dimension $n$. Then the same two assertions hold for $F'$ in place of $F$, for every field $k$, every $s \colon \operatorname{Spec} k \to T$ and every two-affine open cover of $X_s$.
--
--   This is the invariance, under isomorphism of the module, of the fibrewise hypotheses ($H^1$ vanishing and $h^0 = n$ on each two-chart Čech complex) used in the cohomology-and-base-change statements for relative Picard bundles. It is used to carry those hypotheses across the module identifications occurring in the construction of theta bundles, specifically in [`AlgebraicGeometry.RelPicard.nonempty_thetaBundle_tensor_pointSubBasepoint_tensor_pullback_iso`](thm.html#AlgebraicGeometry.RelPicard.nonempty_thetaBundle_tensor_pointSubBasepoint_tensor_pullback_iso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelPicard_forall_subsingleton_H1_and_finrank_H0_fibreModule_of_iso.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.forall_subsingleton_H1_and_finrank_H0_fibreModule_of_iso
    {R : Type u} [CommRing R] {C T : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (t : T ⟶ Spec (CommRingCat.of R)) {F F' : (pullback c t).Modules} (e : F ≅ F') (n : ℕ)
    (h : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F)).H0 = n) :
    ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F')).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s F')).H0 = n := by sorry
