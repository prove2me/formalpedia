-- Prove2me | Theorems.Thm_AutomorphicForm_coe_finComponent_glFin_centralScalar_localUnit_mul_diagUnits2
-- name    : AutomorphicForm.coe_finComponent_glFin_centralScalar_localUnit_mul_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/9d6f4cf5-928d-5e2b-99f3-2752d1a7a9da
-- title:
--   v-component of a central local unit times diag(u,1)
-- statement:
--   Let $K$ be a number field, let $v$ be a height one prime of the ring of integers $\mathcal{O}_K$, let $t$ be a unit of the completion $K_v$, and let $u \in K^\times$. Form the finite idele `localUnit` $(t)$, whose component at $v$ is $t$ and whose component at every other finite place is $1$; include it into the idele group by `finIncl`, which puts $1$ in the infinite part; and let `centralScalar` send this idele to the corresponding central element $\mathrm{diag}(\cdot,\cdot)$ of $GL_2(\mathbb{A}_K)$, i.e. the scalar matrix given by `Matrix.GeneralLinearGroup.scalar`. Multiply this central element, in $GL_2(\mathbb{A}_K)$, by `diagUnits2` applied to the image of $u$ under $K^\times \to \mathbb{A}_K^\times$ and to $1$, that is by the diagonal matrix with entries the idele $u$ and $1$. The assertion is that projecting this element of $GL_2(\mathbb{A}_K)$ to $GL_2$ of the finite adeles (`glFin`, discarding the archimedean part) and then evaluating at $v$ (`finComponent`) yields, as a matrix over $K_v$, the diagonal matrix with entries $t \cdot u_v$ and $t$, where $u_v$ denotes the image of $u$ under $K \to K_v$.
--
--   A component computation for diagonal elements of $GL_2$ over the adeles: it identifies the local behaviour at $v$ of a central local unit multiplied by a split torus element $\mathrm{diag}(u,1)$. It is used in the bookkeeping of orbital-type sums and window integrals over split torus classes in the Langlands–Tunnell part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_coe_finComponent_glFin_centralScalar_localUnit_mul_diagUnits2.lean

import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.coe_finComponent_glFin_centralScalar_localUnit_mul_diagUnits2
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (t : (v.adicCompletion K)ˣ) (u : Kˣ) :
    ((AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K
        (AutomorphicForm.centralScalar (𝓞 K) K
            (Units.map (finIncl (𝓞 K) K : FiniteAdeleRing (𝓞 K) K →* AdeleRing (𝓞 K) K) (localUnit (𝓞 K) K v t)) *
          diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) :
        GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      Matrix.diagonal ![(t : v.adicCompletion K) * algebraMap K (v.adicCompletion K) (u : K), (t : v.adicCompletion K)] := by sorry
