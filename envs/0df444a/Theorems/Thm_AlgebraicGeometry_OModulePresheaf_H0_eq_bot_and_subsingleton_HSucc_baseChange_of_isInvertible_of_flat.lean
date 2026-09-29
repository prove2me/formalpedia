-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_baseChange_of_isInvertible_of_flat
-- name    : AlgebraicGeometry.OModulePresheaf.H0_eq_bot_and_subsingleton_HSucc_baseChange_of_isInvertible_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/2594e99d-d9ec-5262-9495-6022ffd35022
-- title:
--   Base change preserves Čech acyclicity of an invertible module
-- statement:
--   Let $B$ be a commutative ring, $P$ a scheme and $\varpi\colon P\to\operatorname{Spec} B$ a separated morphism, and let $\mathfrak W$ be an ordered affine cover of $P$: a finite linearly ordered index set $\iota$ together with affine opens $U_j$ whose supremum is $\top$. For $i\in\mathbb N$ write $\mathfrak W.\mathrm{Idx}\,i$ for the strictly monotone maps $s\colon \mathrm{Fin}(i+1)\to\iota$ and $\mathfrak W.\mathrm{inter}\,s=\bigwedge_j U_{s(j)}$. Assume that for every such $s$ the ring $\Gamma(P,\mathfrak W.\mathrm{inter}\,s)$, viewed as a $B$-algebra through $\varpi$, is flat as a $B$-module. Let $N$ be a module over $P$ which is invertible in the sense that every point has an open neighbourhood $U$ for which the pullback of $N$ along $U\hookrightarrow P$ is isomorphic to the unit sheaf of modules on $U$. Consider the alternating Čech complex of the presheaf $U\mapsto\Gamma(N,U)$ on $\mathfrak W$, with $i$-cochains the families indexed by $\mathfrak W.\mathrm{Idx}\,i$, and assume that the kernel of $d^0$ is zero and that for every $i$ the quotient $\ker d^{i+1}/\operatorname{im} d^{i}$ is trivial. Then for every commutative $B$-algebra $A$ the same two conclusions hold for the Čech complex of the pullback of $N$ along $\mathrm{pullback.fst}$, over the projection $P\times_{\operatorname{Spec} B}\operatorname{Spec} A\to\operatorname{Spec} A$ and the cover $\mathfrak W.\mathrm{baseChange}\,\varpi\,A$ obtained by pulling back $\mathfrak W$.
--
--   This is the cohomology-and-base-change statement in the form needed here: vanishing of all Čech cohomology of an invertible module on a fixed finite affine cover persists after an arbitrary base change of the base ring, in particular after passage to a fibre. It is used in the study of the relative Picard functor, in the proof that a point of the relative Picard group which is trivial on the zero section becomes, after base change, a tensor-translate of a pullback.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_H0_eq_bot_and_subsingleton_HSucc_baseChange_of_isInvertible_of_flat.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.OModulePresheaf.H0_eq_bot_and_subsingleton_HSucc_baseChange_of_isInvertible_of_flat
    {B : Type u} [CommRing B] {P : Scheme.{u}} (ϖ : P ⟶ Spec (CommRingCat.of B)) [IsSeparated ϖ]
    (𝔚 : P.OrderedAffineCover)
    (hflat : ∀ (i : ℕ) (s : 𝔚.Idx i),
      letI := Scheme.TwoAffineOpenCover.algebraOfHom ϖ (𝔚.inter s); Module.Flat B Γ(P, 𝔚.inter s))
    (N : P.Modules) (hN : Scheme.Modules.IsInvertible N)
    (h0 : (OModulePresheaf.ofModules ϖ N).H0 𝔚 = ⊥)
    (hS : ∀ i, Subsingleton ((OModulePresheaf.ofModules ϖ N).HSucc 𝔚 i))
    (A : Type u) [CommRing A] [Algebra B A] :
    (OModulePresheaf.ofModules (Limits.pullback.snd ϖ (Scheme.TwoAffineOpenCover.specMap B A))
        ((Scheme.Modules.pullback (Limits.pullback.fst ϖ (Scheme.TwoAffineOpenCover.specMap B A))).obj N)).H0
        (𝔚.baseChange ϖ A) = ⊥ ∧
      ∀ i, Subsingleton
        ((OModulePresheaf.ofModules (Limits.pullback.snd ϖ (Scheme.TwoAffineOpenCover.specMap B A))
          ((Scheme.Modules.pullback (Limits.pullback.fst ϖ (Scheme.TwoAffineOpenCover.specMap B A))).obj N)).HSucc
          (𝔚.baseChange ϖ A) i) := by sorry
