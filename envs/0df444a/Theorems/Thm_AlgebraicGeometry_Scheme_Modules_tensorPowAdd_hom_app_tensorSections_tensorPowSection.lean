-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_tensorPowAdd_hom_app_tensorSections_tensorPowSection
-- name    : AlgebraicGeometry.Scheme.Modules.tensorPowAdd_hom_app_tensorSections_tensorPowSection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/48c07f2c-6bfd-5497-b411-da317be018b8
-- title:
--   Tensor powers of a section: g^{⊗ m}⊗ g^{⊗ n}↦ g^{⊗(m+n)}
-- statement:
--   Let $X$ be a scheme, let $L$ be an object of $X$'s category of sheaves of modules, let $U$ be an open of $X$, let $g \in \Gamma(L,U)$ be a section of $L$ over $U$, and let $m,n$ be natural numbers. Here `tensorPow L k` is the $k$-fold tensor power formed left-associatedly in the monoidal category of modules on $X$ ($k=0$ giving the unit object and $k+1$ giving `tensorPow L k ⊗ L`), `tensorSections s t` is the section of $L \otimes M$ over $U$ obtained from the elementary tensor $s \otimes_{\Gamma(X,U)} t$ via the comparison morphism from the presheaf tensor product to the sheafified tensor product, `tensorPowSection g k` is the $k$-th tensor power of $g$ ($k=0$ being the section $1 \in \Gamma(X,U)$ viewed in the unit object, and $k+1$ being `tensorSections` of `tensorPowSection g k` with $g$), and `tensorPowAdd L m n` is the isomorphism $L^{\otimes m} \otimes L^{\otimes n} \cong L^{\otimes(m+n)}$ defined by recursion on $n$ (the right unitor for $n=0$; the inverse associator followed by whiskering `tensorPowAdd L m n` on the right by $L$ for $n+1$). The assertion is that the component at $U$ of the forward direction of `tensorPowAdd L m n` carries `tensorSections (tensorPowSection g m) (tensorPowSection g n)` to `tensorPowSection g (m + n)`. No hypothesis is imposed on $L$ or on $g$.
--
--   This is the compatibility of the additivity isomorphism of tensor powers with tensor powers of a single section, i.e. the multiplicativity $g^{\otimes m}\cdot g^{\otimes n} = g^{\otimes (m+n)}$ underlying the graded ring $\bigoplus_n \Gamma(U, L^{\otimes n})$ of sections of $L$. It is used in the construction of the section ring of an invertible module, [`AlgebraicGeometry.GradedOAlgebra.exists_isSectionRing`](thm.html#AlgebraicGeometry.GradedOAlgebra.exists_isSectionRing), where $g$ is a local frame of $L$ on $U$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_tensorPowAdd_hom_app_tensorSections_tensorPowSection.lean

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

theorem AlgebraicGeometry.Scheme.Modules.tensorPowAdd_hom_app_tensorSections_tensorPowSection
    {X : Scheme.{u}} {L : X.Modules} {U : X.Opens} (g : Γ(L, U)) (m n : ℕ) :
    (Scheme.Modules.tensorPowAdd L m n).hom.app U
        (Scheme.Modules.tensorSections (L := L.tensorPow m) (M := L.tensorPow n)
          (Scheme.Modules.tensorPowSection g m) (Scheme.Modules.tensorPowSection g n)) =
      Scheme.Modules.tensorPowSection g (m + n) := by sorry
