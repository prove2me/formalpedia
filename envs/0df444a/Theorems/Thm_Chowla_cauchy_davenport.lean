-- Prove2me | Theorems.Thm_Chowla_cauchy_davenport
-- name    : Chowla.cauchy_davenport
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T18:55:03.31999+00:00
-- url     : https://prove2.me/theorems/65841679-63ae-4134-96c4-0becc0203729
-- title:
--   Cauchy–Davenport theorem (corollary of Chowla's theorem)
-- statement:
--   For nonempty subsets A, B of ℤ/p with p prime, the sumset satisfies |A + B| ≥ min(p, |A| + |B| − 1). This classical 1813/1935 theorem is derived here as an immediate corollary of the stronger Chowla theorem for composite moduli: when |A| + |B| ≤ p the unit hypothesis is automatic since ℤ/p is a field, and when |A| + |B| > p a pigeonhole argument shows A + B is all of ℤ/p. (Mathlib also contains an independent proof of the prime case; this problem targets the corollary of the composite-modulus theorem.)
-- source:
--   A.-L. Cauchy (1813); H. Davenport (1935). Composite-modulus generalization: S. Chowla (1935); Nathanson arXiv:2407.12253 §7

import Mathlib
open scoped Pointwise

namespace Chowla

/-- **Cauchy–Davenport**: for nonempty `A, B ⊆ ℤ/p` with `p` prime,
`|A + B| ≥ min(p, |A| + |B| - 1)`. Derived here as a corollary of Chowla's theorem
(the composite-modulus generalization), where the prime case supplies the unit
hypothesis automatically. -/
theorem cauchy_davenport {p : ℕ} (hp : p.Prime) {A B : Finset (ZMod p)}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    min p (A.card + B.card - 1) ≤ (A + B).card := by
  sorry

end Chowla
