-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_fppfKummerRow_naturality
-- name    : AlgebraicGeometry.Scheme.fppfKummerRow_naturality
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/7dca2cb1-0138-5be3-a45c-192fe6483ad2
-- title:
--   Naturality of the fppf Kummer row under endomorphisms
-- statement:
--   Let $G$ be a sheaf of abelian groups (valued in `Ab.{1}`) on the small fppf site of $\operatorname{Spec}\mathbf Z$, i.e. on the category of schemes over $\operatorname{Spec}\mathbf Z$ whose structure morphism is flat and locally of finite presentation, equipped with the small fppf Grothendieck topology; let $n\in\mathbf Z$, write $n\bullet\mathrm{id}_G$ for the $n$-fold multiple of the identity endomorphism, and assume that the short complex $\ker(n\bullet\mathrm{id}_G)\xrightarrow{\iota}G\xrightarrow{\,n\,}G$ (with its canonical zero composite) is short exact; let $t\colon G\to G$ be any morphism of sheaves. The assertion is that $(n\bullet\mathrm{id}_G)\circ t=t\circ(n\bullet\mathrm{id}_G)$ holds, and that for the induced endomorphism $t_K=$ `kernel.map` of $\ker(n\bullet\mathrm{id}_G)$ determined by this commutation the following two identities hold in the cohomology groups $H^k$ of the sheaf (defined as the Ext-groups $\mathrm{Ext}^k$ of the sheaf against the constant sheaf $\mathbf Z$, with induced maps given by composition with the degree-zero Ext class of a morphism): for every $x\in H^0(G)$, $\delta(H^0(t)x)=H^1(t_K)(\delta x)$, where $\delta\colon H^0(G)\to H^1(\ker(n\bullet\mathrm{id}_G))$ is the connecting homomorphism [`FppfCohomologyLES.cohomologyδ`](def/AlgebraicGeometry_FppfCohomologyLES.html#L47) attached to the short exact sequence in degrees $0\to 1$; and for every $y\in H^1(\ker(n\bullet\mathrm{id}_G))$, $H^1(\iota)(H^1(t_K)y)=H^1(t)(H^1(\iota)y)$. The commutation relation is packaged as an existential over its proof so that $t_K$ can be named.
--
--   This is the equivariance of the fppf Kummer row $0\to H^0(G)/n\to H^1(G[n])\to H^1(G)[n]\to 0$ over $\operatorname{Spec}\mathbf Z$ under an arbitrary endomorphism of the coefficient sheaf; it makes the row a sequence of modules over any ring acting on $G$, so that it may be localised at a prime of that ring. It is used by [`AlgebraicGeometry.Scheme.exists_shrink_fppfKummerRow_of_epi_zsmul`](thm.html#AlgebraicGeometry.Scheme.exists_shrink_fppfKummerRow_of_epi_zsmul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_fppfKummerRow_naturality.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

theorem AlgebraicGeometry.Scheme.fppfKummerRow_naturality
    (G : Sheaf (smallFppfTopology specInt) Ab.{1}) (n : ℤ)
    (hS : (ShortComplex.mk (kernel.ι (n • 𝟙 G)) (n • 𝟙 G) (kernel.condition (n • 𝟙 G))).ShortExact)
    (t : G ⟶ G) :
    ∃ w : (n • 𝟙 G) ≫ t = t ≫ (n • 𝟙 G),
      (∀ x : fppfCohomology specInt G 0,
        (FppfCohomologyLES.cohomologyδ hS 0 1 rfl :
            fppfCohomology specInt G 0 →+ fppfCohomology specInt (kernel (n • 𝟙 G)) 1)
          (fppfCohomologyMap specInt t 0 x) =
        fppfCohomologyMap specInt (kernel.map (n • 𝟙 G) (n • 𝟙 G) t t w) 1
          ((FppfCohomologyLES.cohomologyδ hS 0 1 rfl :
            fppfCohomology specInt G 0 →+ fppfCohomology specInt (kernel (n • 𝟙 G)) 1) x)) ∧
      (∀ y : fppfCohomology specInt (kernel (n • 𝟙 G)) 1,
        fppfCohomologyMap specInt (kernel.ι (n • 𝟙 G)) 1
            (fppfCohomologyMap specInt (kernel.map (n • 𝟙 G) (n • 𝟙 G) t t w) 1 y) =
          fppfCohomologyMap specInt t 1 (fppfCohomologyMap specInt (kernel.ι (n • 𝟙 G)) 1 y)) := by sorry
