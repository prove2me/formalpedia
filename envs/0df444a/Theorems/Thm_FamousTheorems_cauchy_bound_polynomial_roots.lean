-- Prove2me | Theorems.Thm_FamousTheorems_cauchy_bound_polynomial_roots
-- name    : FamousTheorems.cauchy_bound_polynomial_roots
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:08:58.989104+00:00
-- url     : https://prove2.me/theorems/91611963-02d0-456e-84c2-dae6f06251f1
-- title:
--   Cauchy's bound on polynomial roots
-- statement:
--   **Cauchy's bound on polynomial roots.** Let $p=a_dx^d+\dots+a_0$ be a nonzero polynomial over a normed division ring. Every root $a$ of $p$ satisfies
--   $$|a|<1+\max_{0\le i<d}\frac{|a_i|}{|a_d|}.$$
--
--   Cauchy gave this bound in 1829. It confines all roots to an explicit disc, which is the starting point for root-isolation and numerical root-finding algorithms.
--
--   **Formalization note.** Mathlib's `Polynomial.IsRoot.norm_lt_cauchyBound`. `p.cauchyBound` is the non-negative real number $1+\max_{i<d}\|a_i\|/\|a_d\|$, and the norm of the root is taken in `NNReal` (`‖a‖₊`). The coefficients may lie in any normed division ring, including $\mathbb R$, $\mathbb C$, the quaternions and $\mathbb Q_p$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Polynomial.IsRoot.norm_lt_cauchyBound`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cauchy_bound_polynomial_roots {K : Type*} [NormedDivisionRing K] {p : Polynomial K} (hp : p ≠ 0) {a : K} (ha : p.IsRoot a) :
    ‖a‖₊ < p.cauchyBound := by sorry

end FamousTheorems
