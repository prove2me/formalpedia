-- Prove2me | Theorems.Thm_AvgValueAlloc_eq_4
-- name    : AvgValueAlloc.eq_4
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T11:39:07.511598+00:00
-- url     : https://prove2.me/theorems/83c306d6-e466-4c43-885d-44cbeff6e982
-- title:
--   (4): $\mathrm{OPT}_{\mathrm{off}}(Q)\le T\,P(Q)$
-- statement:
--   Let $\rho\in\mathbb Q^n_{>0}$ and let $Q=(v_1,\dots,v_T)$ be a live sequence. With $P(v)=\max\{v_j:v_j\ge\rho_j\}$ ($0$ if none) and $P(Q)=\sum_t P(v_t)$,
--   $$
--   \mathrm{OPT}_{\mathrm{off}}(Q)\le T\,P(Q).\tag{4}
--   $$
--   An assigned negative needs a positive at its buyer, so every assigned value is at most $P(Q)$. This is what the positive-only branch pays for: it realizes $P(Q)$ and so earns factor $T$.
--
--   Differences from the source:
--   - encoding: live multiset Q → a sequence Q : Fin T → Vec n; reason: OPT_off depends only on the multiset; same instances
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §2, p.4, eq. (4)

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_OPToff
import Definitions.Def_AvgValueAlloc_posVal

namespace AvgValueAlloc

open scoped ENNReal

/-- **(4): offline welfare is at most `T · P(Q)`.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §2, p.4: "Positive-only allocation realizes P(A) from zero
surplus. An assigned negative requires a positive at its buyer, so its value is at most P(Q);
positive welfare totals at most P(Q). Thus, including the case of no positive edge,
OPT_off(Q) ≤ TP(Q). (4)"

For thresholds `ρ > 0` and a live sequence `Q` of `T` items,
`OPT_off(Q) ≤ T · Σ_t P(Q_t)` with `P(v) = max {v_j : v_j ≥ ρ_j}` (`0` if none).

**Formalization Note.** `OPT_off` is in `ℝ≥0∞`; `P(Q)` is a real sum cast by `ENNReal.ofReal`. -/
theorem eq_4 {n T : ℕ} (ρ : Fin n → ℚ) (hρ : ∀ j, 0 < ρ j) (Q : Fin T → Vec n) :
    OPToff ρ Q ≤ (T : ℝ≥0∞) * ENNReal.ofReal (posValSum ρ Q) := by sorry

end AvgValueAlloc
