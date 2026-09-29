-- Prove2me | Theorems.Thm_AutomorphicForm_glArch_centralScalar_mul_diagUnits2
-- name    : AutomorphicForm.glArch_centralScalar_mul_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/ce7acd08-a015-5fc7-ba5c-b6b24a62ee4d
-- title:
--   Archimedean component of scalar(z)cdotdiag(a,b)
-- statement:
--   Let $K$ be a number field, with ring of integers $\mathcal{O}_K$, and let $z, a, b$ be units of the adele ring $\mathbb{A}_K$ of $K$. Write $\mathtt{adeleArch}$ for the ring homomorphism $\mathbb{A}_K \to K_\infty$ sending an adele to its infinite component (the first coordinate of the product decomposition of the adele ring), and $\mathtt{glArch}$ for the induced group homomorphism $\mathrm{GL}_2(\mathbb{A}_K) \to \mathrm{GL}_2(K_\infty)$ obtained by applying this map entrywise. Further, $\mathtt{centralScalar}$ sends a unit $u$ of $\mathbb{A}_K$ to the scalar matrix $u \cdot I_2$ in $\mathrm{GL}_2(\mathbb{A}_K)$, and $\mathtt{diagUnits2}\,x\,y$ denotes the element of $\mathrm{GL}_2$ with matrix $\mathrm{diag}(x,y)$ and inverse matrix $\mathrm{diag}(x^{-1},y^{-1})$. The assertion is that the archimedean component of the product $\mathrm{scalar}(z)\cdot\mathrm{diag}(a,b)$ equals $\mathrm{scalar}(z_\infty)\cdot\mathrm{diag}(a_\infty,b_\infty)$, where $z_\infty, a_\infty, b_\infty$ are the images of $z, a, b$ under the map on unit groups induced by $\mathtt{adeleArch}$. Both diagonal entries are allowed to be arbitrary units; no normalisation $b = 1$ is imposed.
--
--   A bookkeeping identity recording that passage to the archimedean component commutes with the parametrisation of the centre and of the diagonal split torus in $\mathrm{GL}_2(\mathbb{A}_K)$. It is used in the analysis of orbital integrals and of archimedean matching conditions for adelic automorphic forms, where torus elements are decomposed into a central factor and a diagonal factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_glArch_centralScalar_mul_diagUnits2.lean

import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.glArch_centralScalar_mul_diagUnits2
    (K : Type) [Field K] [NumberField K] (z a b : (AdeleRing (𝓞 K) K)ˣ) :
    AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 a b) =
      Matrix.GeneralLinearGroup.scalar (Fin 2)
          (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) z) *
        diagUnits2 (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) a)
          (Units.map (AdelicLevel.adeleArch (𝓞 K) K : AdeleRing (𝓞 K) K →* InfiniteAdeleRing K) b) := by sorry
