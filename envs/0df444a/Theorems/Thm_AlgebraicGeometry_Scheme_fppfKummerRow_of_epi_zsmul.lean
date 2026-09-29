-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_fppfKummerRow_of_epi_zsmul
-- name    : AlgebraicGeometry.Scheme.fppfKummerRow_of_epi_zsmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/7980f1fa-be83-539b-8fca-4581e2cb2335
-- title:
--   Kummer row in fppf cohomology over Specℤ
-- statement:
--   Let $G$ be a sheaf of abelian groups (valued in $\mathrm{Ab}$ of the next universe) on the small fppf site of $\operatorname{Spec}\mathbf{Z}$, that is, on the site whose objects are $\operatorname{Spec}\mathbf{Z}$-schemes whose structure morphism is flat and locally of finite presentation, with the associated small Grothendieck topology; let $n \in \mathbf{Z}$ and assume that $n \cdot \mathrm{id}_G$ is an epimorphism of sheaves. Writing $\iota$ for the canonical map $\ker(n \cdot \mathrm{id}_G) \to G$, the assertion is that there exists a proof `hS` that the short complex $\ker(n\cdot\mathrm{id}_G) \xrightarrow{\iota} G \xrightarrow{n} G$ (with zero composite given by the kernel condition) is short exact, such that, for the connecting homomorphism $\delta =$ [`FppfCohomologyLES.cohomologyδ hS 0 1 rfl`](def/AlgebraicGeometry_FppfCohomologyLES.html#L47) from $H^0(\operatorname{Spec}\mathbf{Z}, G)$ to $H^1(\operatorname{Spec}\mathbf{Z}, \ker(n\cdot\mathrm{id}_G))$ and for the map $\iota_*$ induced by $\iota$ on $H^1$ (given by composition with $\mathrm{Ext}$-class of $\iota$), the three following hold: the kernel of $\delta$ is the image of multiplication by $n$ on $H^0(\operatorname{Spec}\mathbf{Z}, G)$; the pair $(\delta, \iota_*)$ is exact as a sequence of additive maps; and the image of $\iota_*$ is the kernel of multiplication by $n$ on $H^1(\operatorname{Spec}\mathbf{Z}, G)$. Here $H^k(\operatorname{Spec}\mathbf{Z}, -)$ denotes the fppf cohomology groups `fppfCohomology`, defined as the sheaf cohomology $\mathrm{Ext}$-groups of the sheaf in question.
--
--   This is the Kummer exact row $0 \to H^0(G)/n \to H^1(G[n]) \to H^1(G)[n] \to 0$ in fppf cohomology over $\operatorname{Spec}\mathbf{Z}$, in the form of the three statements about the connecting map and the map induced by $G[n] \hookrightarrow G$. It is applied to commutative group schemes over $\mathbf{Z}$ for which multiplication by $n$ is flat and surjective, and is used by [`AlgebraicGeometry.Scheme.exists_shrink_fppfKummerRow_of_epi_zsmul`](thm.html#AlgebraicGeometry.Scheme.exists_shrink_fppfKummerRow_of_epi_zsmul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_fppfKummerRow_of_epi_zsmul.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

theorem AlgebraicGeometry.Scheme.fppfKummerRow_of_epi_zsmul
    (G : Sheaf (smallFppfTopology specInt) Ab.{1}) (n : ℤ) (hn : Epi (n • 𝟙 G)) :
    ∃ hS : (ShortComplex.mk (kernel.ι (n • 𝟙 G)) (n • 𝟙 G) (kernel.condition (n • 𝟙 G))).ShortExact,
      (FppfCohomologyLES.cohomologyδ hS 0 1 rfl :
          fppfCohomology specInt G 0 →+ fppfCohomology specInt (kernel (n • 𝟙 G)) 1).ker =
        (n • AddMonoidHom.id (fppfCohomology specInt G 0)).range ∧
      Function.Exact
        (FppfCohomologyLES.cohomologyδ hS 0 1 rfl :
          fppfCohomology specInt G 0 →+ fppfCohomology specInt (kernel (n • 𝟙 G)) 1)
        (fppfCohomologyMap specInt (kernel.ι (n • 𝟙 G)) 1) ∧
      (fppfCohomologyMap specInt (kernel.ι (n • 𝟙 G)) 1).range =
        AddMonoidHom.ker (n • AddMonoidHom.id (fppfCohomology specInt G 1)) := by sorry
