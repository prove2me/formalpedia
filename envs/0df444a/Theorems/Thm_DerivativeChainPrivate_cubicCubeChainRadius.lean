-- Prove2me | Theorems.Thm_DerivativeChainPrivate_cubicCubeChainRadius
-- name    : DerivativeChainPrivate.cubicCubeChainRadius
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-19T14:41:36.541394+00:00
-- url     : https://prove2.me/theorems/ca2a3e90-459f-49c5-90a5-8e037323ac89
-- title:
--   Complete derivative-zero chains for cubes of complex cubics
-- statement:
--   Let $q$ be any monic complex cubic and let all its roots lie in a disk of radius $R\ge0$ centered at an arbitrary complex point $o$. There exists a complete chain $z_1,\ldots,z_9$ through the actual ordinary derivative rows of $q^3$: $D^{9-m}(q^3)(z_m)=0$ for every $1\le m\le9$. Its length satisfies $$\sum_{m=1}^{8}|z_{m+1}-z_m|\le\frac{4\sqrt2}{3}R.$$ The initial point is the centroid of the three source roots, counted with multiplicity. The final three points coincide at one root of $q$. Both coordinates are nondecreasing in one common orthonormal coordinate frame. In the formal statement the frame is encoded by unit complex coefficients $a,b$ with $\operatorname{Re}(a\overline b)=0$, acting by $z\mapsto\operatorname{Re}(az)$ and $z\mapsto\operatorname{Re}(bz)$. Such a frame is a rotation, possibly composed with a reflection; translation adds only constant coordinate offsets. Arbitrary complex coefficients, repeated roots, zero quadratic moment, and zero radius are included. No root prefix, analytic inverse, continuation, or genericity hypothesis is assumed. This is the cube-of-a-cubic class result, not the fourth-power result or either unrestricted prize question.
-- source:
--   Derivative-zero chains: public formalization reference, R60, DerivativeChainPrivate.cubicCubeChainRadius. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false

theorem DerivativeChainPrivate.cubicCubeChainRadius (q : Polynomial ℂ) (hq : q.Monic) (hdeg : q.natDegree = 3)
    (o : ℂ) (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x : ℂ, q.eval x = 0 → ‖x-o‖ ≤ R) :
    ∃ (z : Fin 9 → ℂ) (a b : ℂ),
      (∀ i, (derivative^[9-(i.val+1)] (q^3)).eval (z i) = 0) ∧
      z 0 = q.roots.sum/3 ∧ z 6 = z 7 ∧ z 7 = z 8 ∧ q.eval (z 8) = 0 ∧
      ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ (a*starRingEnd ℂ b).re = 0 ∧
      Monotone (fun i => (a*z i).re) ∧ Monotone (fun i => (b*z i).re) ∧
      chainCost z ≤ 4*Real.sqrt 2*R/3 := by sorry
