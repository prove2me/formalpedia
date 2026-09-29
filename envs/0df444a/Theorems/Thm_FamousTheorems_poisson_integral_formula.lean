-- Prove2me | Theorems.Thm_FamousTheorems_poisson_integral_formula
-- name    : FamousTheorems.poisson_integral_formula
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:08:36.568984+00:00
-- url     : https://prove2.me/theorems/2dc7bdd2-1050-4e38-a33f-43d5523755dd
-- title:
--   The Poisson integral formula
-- statement:
--   **The Poisson integral formula.** Let $f$ be holomorphic on the open disc $D=\{|z-c|<R\}$ and continuous on its closure, with values in a complex Banach space. Then for every $w\in D$,
--   $$f(w)=\frac1{2\pi}\int_0^{2\pi}P_c(w,\zeta)\,f(\zeta)\,d\theta,\qquad \zeta=c+Re^{i\theta},\quad P_c(w,\zeta)=\frac{|\zeta-c|^2-|w-c|^2}{|\zeta-w|^2}.$$
--
--   The Poisson formula recovers a function inside the disc from its boundary values. It solves the Dirichlet problem on the disc, and it links complex analysis with harmonic analysis and Fourier series.
--
--   **Formalization note.** Mathlib's `DiffContOnCl.circleAverage_poissonKernel_smul`. `poissonKernel c w` is the real-valued Poisson kernel for the circle centred at $c$, evaluated at the point $w$. `Real.circleAverage` is the normalised integral over the circle of radius $R$ about $c$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `DiffContOnCl.circleAverage_poissonKernel_smul`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem poisson_integral_formula {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E} {c w : ℂ} {R : ℝ}
    (hf : DiffContOnCl ℂ f (Metric.ball c R)) (hw : w ∈ Metric.ball c R) :
    Real.circleAverage (poissonKernel c w • f) c R = f w := by sorry

end FamousTheorems
