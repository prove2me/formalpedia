-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_pullbackCongr_pasteSquares_app
-- name    : AlgebraicGeometry.Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/748c2c09-09e2-51e6-acc4-001aad16e782
-- title:
--   Pasting law for base-change isomorphisms of module pullbacks
-- statement:
--   Let $X,X_0,X_1,Y,Y_0,Y_1$ be schemes, and let $a\colon X_0\to X_1$, $b\colon X_1\to X$, $d\colon X_0\to X$ be morphisms with $e$ a proof that $b\circ a=d$; let $s_0\colon Y_0\to X_0$, $s_1\colon Y_1\to X_1$, $s\colon Y\to X$ and $r\colon Y_0\to Y_1$, $p\colon Y_1\to Y$, $m\colon Y_0\to Y$ be morphisms with $G$ a proof that $p\circ r=m$, and let $E$, $F$, $H$ be proofs of the commutativities $a\circ s_0=s_1\circ r$, $b\circ s_1=s\circ p$ and $d\circ s_0=s\circ m$ (so that $E$ and $F$ are two squares stacked along the edge $s_1$, and $H$ is the outer square; $H$ is in fact forced by $E,F,e,G$, but is taken as an argument so that the outer base-change isomorphism can be formed). Writing $f^*$ for `Scheme.Modules.pullback f`, $c_{f,g}\colon f^*g^*\xrightarrow{\sim}(g\circ f)^*$ for the composition isomorphism `pullbackComp` followed by `pullbackCongr` rewriting the composite along the given equality, and $\beta$ for the base-change isomorphism of a square, obtained as $c$ followed by `pullbackCongr` of the square and then the inverse of $c$, the assertion is that for every sheaf of $\mathcal O_X$-modules $M$ the two morphisms $s_0^*a^*b^*M\to m^*s^*M$ agree: $\beta_E$ at $b^*M$, followed by $r^*$ applied to $\beta_F$ at $M$, followed by $c_{r,p}$ at $s^*M$, equals $s_0^*$ applied to $c_{a,b}$ at $M$, followed by $\beta_H$ at $M$.
--
--   This is the pasting (coherence) law for the inverse-image pseudofunctor $X\mapsto\mathbf{Mod}(\mathcal O_X)$, $f\mapsto f^*$: pasting the base-change isomorphisms of two stacked squares and collapsing $r^*p^*$ to $m^*$ gives the base-change isomorphism of the outer square, after $a^*b^*$ has been collapsed to $d^*$. It is used in the descent and gluing arguments for rigidified line bundles in the construction of the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_pullbackComp_pullbackCongr_pasteSquares_app.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.pullbackComp_pullbackCongr_pasteSquares_app
    {X X₀ X₁ Y Y₀ Y₁ : Scheme.{u}}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X) (d : X₀ ⟶ X) (e : a ≫ b = d)
    (s₀ : Y₀ ⟶ X₀) (s₁ : Y₁ ⟶ X₁) (s : Y ⟶ X)
    (r : Y₀ ⟶ Y₁) (p : Y₁ ⟶ Y) (m : Y₀ ⟶ Y) (G : r ≫ p = m)
    (E : s₀ ≫ a = r ≫ s₁) (F : s₁ ≫ b = p ≫ s) (H : s₀ ≫ d = m ≫ s) (M : X.Modules) :
    (Scheme.Modules.pullbackComp s₀ a ≪≫ Scheme.Modules.pullbackCongr E ≪≫
          (Scheme.Modules.pullbackComp r s₁).symm).hom.app ((Scheme.Modules.pullback b).obj M) ≫
      (Scheme.Modules.pullback r).map
          ((Scheme.Modules.pullbackComp s₁ b ≪≫ Scheme.Modules.pullbackCongr F ≪≫
            (Scheme.Modules.pullbackComp p s).symm).hom.app M) ≫
        (Scheme.Modules.pullbackComp r p ≪≫ Scheme.Modules.pullbackCongr G).hom.app
          ((Scheme.Modules.pullback s).obj M) =
      (Scheme.Modules.pullback s₀).map
          ((Scheme.Modules.pullbackComp a b ≪≫ Scheme.Modules.pullbackCongr e).hom.app M) ≫
        (Scheme.Modules.pullbackComp s₀ d ≪≫ Scheme.Modules.pullbackCongr H ≪≫
          (Scheme.Modules.pullbackComp m s).symm).hom.app M := by sorry
