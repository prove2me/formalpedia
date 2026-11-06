-- Prove2me | solution 1 for hh_deriv
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T21:52:48.203012+00:00
-- url     : https://prove2.me/submissions/64e04d3e-83f9-45f2-8d72-f7698d8cb107

import Definitions.Def_PrimeNumberTheoremAnd_Wiener

set_option autoImplicit true
open Real

theorem solution (a : ℝ) {t : ℝ} (ht : t ≠ 0) : HasDerivAt (hh a) (hh' a t) t := by
  have hlog : HasDerivAt (fun x : ℝ => a * Real.log x) (a * t⁻¹) t :=
    (Real.hasDerivAt_log ht).const_mul a
  have hsq : HasDerivAt (fun x : ℝ => (a * Real.log x) ^ 2)
      (2 * (a * Real.log t) * (a * t⁻¹)) t := by
    convert hlog.pow 2 using 1 <;>
      try { apply Subsingleton.elim } <;>
      try { ext x; simp only [Pi.pow_apply] } <;>
      ring

  have hinner : HasDerivAt (fun x : ℝ => 1 + (a * Real.log x) ^ 2)
      (2 * (a * Real.log t) * (a * t⁻¹)) t := hsq.const_add 1
  have hden : HasDerivAt (fun x : ℝ => x * (1 + (a * Real.log x) ^ 2))
      ((1 + (a * Real.log t) ^ 2) + t * (2 * (a * Real.log t) * (a * t⁻¹))) t := by
    convert (hasDerivAt_id t).mul hinner using 1 <;>
      try { apply Subsingleton.elim } <;>
      try { ext x; simp only [Pi.mul_apply, id_eq] } <;>
      simp only [id_eq] <;>
      ring

  have hnonzero : 1 + (a * Real.log t) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (a * Real.log t)]
  have heq :
      -((1 + (a * Real.log t) ^ 2) + t * (2 * (a * Real.log t) * (a * t⁻¹))) /
          (t * (1 + (a * Real.log t) ^ 2)) ^ 2 = hh' a t := by
    simp only [hh', hh, pp]
    field_simp [ht, hnonzero]
    ring
  rw [← heq]
  change HasDerivAt (fun x : ℝ => (x * (1 + (a * Real.log x) ^ 2))⁻¹) _ t
  convert hden.inv (mul_ne_zero ht hnonzero) using 1 <;>
    try { apply Subsingleton.elim } <;>
    try { ext x; simp only [Pi.inv_apply] }
