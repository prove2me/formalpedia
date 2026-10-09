-- Prove2me | Theorems.Thm_AffineVolterra_Transform_lemma_4_4
-- name    : AffineVolterra.Transform.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:56:17.308392+00:00
-- url     : https://prove2.me/theorems/8c92bbb6-2f06-4445-b848-cf9776093900
-- title:
--   Lemma 4.4 — resolvent form of the Riccati–Volterra equation
-- statement:
--   In the affine Volterra setting, let $R_B$ be the second-kind resolvent of $-KB$ and set $E_B=K-R_B*K$. For $f\in L^1([0,T])$ and $\psi\in L^2([0,T])$, the Riccati–Volterra equation (4.3) holds if and only if
--
--   $$
--   \psi=uE_B+\bigl(f+\tfrac12 A(\psi)\bigr)*E_B.
--   $$
--
--   This removes the linear $\psi B$ term while retaining the quadratic affine term. Both convolution equations include integrability of their integrands and hold almost everywhere on $[0,T]$.
-- source:
--   Abi Jaber, Larsson and Pulido, Affine Volterra processes, arXiv:1708.08796v3, Lemma 4.4, p. 19

import Mathlib
import Definitions.Def_AffineVolterra_Transform_Setting

open MeasureTheory

namespace AffineVolterra.Transform

/-- Lemma 4.4, p. 19: equations (4.3) and (4.8) are equivalent. -/
theorem lemma_4_4 {d : ℕ} (K R_B : RKernel d) (D : AffineData d)
    (T : ℝ) (u : CVec d) (f ψ : ℝ → CVec d)
    (hd : 0 < d) (hT : 0 ≤ T)
    (hK : KernelLpLoc 2 K)
    (hR : IsResolvent (fun t => -kernelRight K (Bmat D) t) R_B) :
    IsRiccati43 K D T u f ψ ↔ IsRiccati48 K R_B D T u f ψ := by sorry

end AffineVolterra.Transform
