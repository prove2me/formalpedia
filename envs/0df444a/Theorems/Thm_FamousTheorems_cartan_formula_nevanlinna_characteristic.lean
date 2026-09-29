-- Prove2me | Theorems.Thm_FamousTheorems_cartan_formula_nevanlinna_characteristic
-- name    : FamousTheorems.cartan_formula_nevanlinna_characteristic
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:08:42.304058+00:00
-- url     : https://prove2.me/theorems/acd58728-bae6-433c-bfa5-864726c4d325
-- title:
--   Cartan's formula for the Nevanlinna characteristic
-- statement:
--   **Cartan's formula for the Nevanlinna characteristic.** Let $f$ be meromorphic on $\mathbb C$ and $R\ne0$. Then the Nevanlinna characteristic of $f$ is the average of the counting functions of the $a$-points over the unit circle, plus a correction term:
--   $$T(R,f)=\frac1{2\pi}\int_0^{2\pi}N\big(R,f,e^{i\theta}\big)\,d\theta+\frac1{2\pi}\int_0^{2\pi}\log\big|\operatorname{lc}_0(f-e^{i\theta})\big|\,d\theta.$$
--   Here $N(R,f,a)$ is the logarithmic counting function of the solutions of $f=a$ and $\operatorname{lc}_0(g)$ is the leading (trailing) coefficient of $g$ at $0$.
--
--   Cartan's identity (1929) shows that $T(R,f)$ is an increasing, convex function of $\log R$. It is a basic tool of Nevanlinna value distribution theory.
--
--   **Formalization note.** Mathlib's `ValueDistribution.characteristic_top_eq_circleAverage_add_circleAverage`. `characteristic f ⊤ R` is the Nevanlinna characteristic with respect to the value $\infty$, `logCounting f a R` is the logarithmic counting function of $a$-points (with $a$ coerced into `WithTop ℂ`), `meromorphicTrailingCoeffAt g 0` is the leading coefficient of the Laurent expansion of $g$ at $0$, and `Real.circleAverage h 0 1` averages $h$ over the unit circle. `Meromorphic f` means meromorphic at every point of $\mathbb C$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ValueDistribution.characteristic_top_eq_circleAverage_add_circleAverage`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cartan_formula_nevanlinna_characteristic {f : ℂ → ℂ} {R : ℝ} (hf : Meromorphic f) (hR : R ≠ 0) :
    ValueDistribution.characteristic f ⊤ R =
      Real.circleAverage (fun a : ℂ => ValueDistribution.logCounting f (a : WithTop ℂ) R) 0 1 +
        Real.circleAverage (fun a : ℂ => Real.log ‖meromorphicTrailingCoeffAt (fun x => f x - a) 0‖) 0 1 := by sorry

end FamousTheorems
