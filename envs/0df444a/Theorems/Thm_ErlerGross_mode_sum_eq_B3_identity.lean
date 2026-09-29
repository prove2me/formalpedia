-- Prove2me | Theorems.Thm_ErlerGross_mode_sum_eq_B3_identity
-- name    : ErlerGross.mode_sum_eq_B3_identity
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T10:03:20.565833+00:00
-- url     : https://prove2.me/theorems/4f38c569-d602-4204-82d0-d2a69a79364a
-- title:
--   Mode series equals twice the B.3 scalar series
-- statement:
--   The mode series in Erler–Gross Eq. (B.3) has sum twice the scalar series displayed there:
--
--   \sum_{n\ge 1}3m_{2n}\beta_{2n}=2\sum_{n\ge 1}\left(\frac{2}{2n-1}-\frac{1}{2n-\frac23}-\frac{1}{2n-\frac43}\right).
--
--   In the Lean indexing, both sums start at index +1$ for \in\mathbb N$. The scalar-series summand is ErlerGross.b3Term; the mode summand uses
--   eumannMEven and etaVec. This is the identity component of the formalized Eq. (B.3).
-- source:
--   T. G. Erler and D. J. Gross, Locality, Causality, and an Initial Value Formulation for Open String Field Theory, arXiv:hep-th/0406199v2 (2004), Appendix B, eq. (B.3), p. 46

import Definitions.Def_ErlerGross_defs
open Real Filter Topology MeasureTheory
open ErlerGross

namespace ErlerGross
theorem mode_sum_eq_B3_identity :
    HasSum (fun n : ℕ => 3 * neumannMEven (n + 1) * betaVec (2 * (n + 1)))
      (2 * ∑' n : ℕ, b3Term (n + 1)) := by
  sorry
end ErlerGross
