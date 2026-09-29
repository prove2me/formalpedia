-- Prove2me | Theorems.Thm_CategoryTheory_ShortComplex_ShortExact_extClass_eq_zero_iff_exists_section_g
-- name    : CategoryTheory.ShortComplex.ShortExact.extClass_eq_zero_iff_exists_section_g
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/272b96e1-4316-5ed9-a7b1-207b0acc419c
-- title:
--   extClass = 0 iff g admits a section
-- statement:
--   Let $C$ be an abelian category (with a choice of universe for its morphism classes) which is equipped with an `Ext` theory in the sense of Mathlib's `HasExt` class for a universe $w$, so that $\operatorname{Ext}^n(X,Y)$ is a $w$-small type of Yoneda extension classes. Let $S$ be a short complex $S.X_1 \xrightarrow{S.f} S.X_2 \xrightarrow{S.g} S.X_3$ in $C$, and let `hS` be a proof that $S$ is short exact, i.e. that $S.f$ is a monomorphism, $S.g$ is an epimorphism and $S$ is exact at the middle term. Associated with `hS` is the class `hS.extClass` in $\operatorname{Ext}^1(S.X_3, S.X_1)$. The theorem asserts the equivalence of two statements: that `hS.extClass` is the zero element of $\operatorname{Ext}^1(S.X_3, S.X_1)$, and that there exists a morphism $s : S.X_3 \to S.X_2$ in $C$ with $s$ followed by $S.g$ equal to the identity of $S.X_3$, i.e. that $S.g$ admits a section. No splitting of $S.f$ or direct-sum decomposition of $S.X_2$ is asserted; the right-hand side is exactly the existence of a section of $S.g$.
--
--   This is Yoneda's characterisation of trivial extensions: an extension class vanishes in $\operatorname{Ext}^1$ precisely when the surjection splits. It is used in the fppf-cohomological part of the development, for the vanishing of the extension class attached to $\mathbf{G}_m$ and for the triviality of the first fppf cohomology of a constant $\mathbf{Z}/p$ over $\operatorname{Spec}\mathbf{Z}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CategoryTheory_ShortComplex_ShortExact_extClass_eq_zero_iff_exists_section_g.lean

import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe w v u
open CategoryTheory Abelian Limits

theorem CategoryTheory.ShortComplex.ShortExact.extClass_eq_zero_iff_exists_section_g
    {C : Type u} [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C]
    [CategoryTheory.HasExt.{w} C] {S : CategoryTheory.ShortComplex C} (hS : S.ShortExact) :
    hS.extClass = 0 ↔ ∃ s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 S.X₃ := by sorry
