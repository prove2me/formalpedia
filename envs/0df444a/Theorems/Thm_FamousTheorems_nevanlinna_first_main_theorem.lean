-- Prove2me | Theorems.Thm_FamousTheorems_nevanlinna_first_main_theorem
-- name    : FamousTheorems.nevanlinna_first_main_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:26:30.48424+00:00
-- url     : https://prove2.me/theorems/d5bf076f-c1a2-4c02-952a-756b4cccce04
-- title:
--   The first main theorem of value distribution theory (Nevanlinna)
-- statement:
--   **The first main theorem of Nevanlinna theory.** Let $f$ be meromorphic on $\mathbb C$, with Nevanlinna characteristic function $T(r,f)=m(r,f)+N(r,f)$ (the proximity function plus the logarithmic counting function of poles). Then for every $r$,
--   $$\big|\,T(r,f)-T(r,1/f)\,\big|\le\max\big(|\log|f(0)||,\ |\log|c_0||\big),$$
--   where $c_0$ is the leading (trailing) coefficient of the Laurent expansion of $f$ at $0$. In particular $T(r,1/f)=T(r,f)+O(1)$.
--
--   Applied to $f-a$ in place of $f$, this shows that $m(r,a)+N(r,a)$ is the same up to a bounded term for every value $a$. It is the starting point of Nevanlinna's value distribution theory, whose second main theorem refines Picard's theorem.
--
--   **Formalization note.** Mathlib's `ValueDistribution.characteristic_sub_characteristic_inv_le`. `ValueDistribution.characteristic f ⊤ R` is $T(R,f)$ for the value $\infty$, and `meromorphicTrailingCoeffAt f 0` is the leading coefficient of the Laurent expansion at $0$ (it equals $f(0)$ when $f$ is analytic and nonzero at $0$). `Meromorphic f` means meromorphic at every point of $\mathbb C$. The statement gives the version with value $\infty$, relating $f$ and $1/f$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ValueDistribution.characteristic_sub_characteristic_inv_le`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem nevanlinna_first_main_theorem {f : ℂ → ℂ} (hf : Meromorphic f) (R : ℝ) :
    |ValueDistribution.characteristic f ⊤ R - ValueDistribution.characteristic f⁻¹ ⊤ R|
      ≤ max |Real.log ‖f 0‖| |Real.log ‖meromorphicTrailingCoeffAt f 0‖| := by sorry

end FamousTheorems
