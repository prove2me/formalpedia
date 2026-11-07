-- Prove2me | Theorems.Thm_AvgValueAlloc_eq_16
-- name    : AvgValueAlloc.eq_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:15.196133+00:00
-- url     : https://prove2.me/theorems/2b00bef6-edd0-48c8-9605-0fc07356ec8a
-- title:
--   (16): $\mathrm{OPT}_{\mathrm{off}}(Q)/4\le\mathrm{OPT}_{\mathrm{inv}}(Q)\le\mathrm{OPT}_{\mathrm{off}}(Q)$
-- statement:
--   Let $\rho\in\mathbb Q^n_{>0}$ and $Q$ a known live multiset in uniform order. The inventory-known causal optimum satisfies
--   $$
--   \frac{\mathrm{OPT}_{\mathrm{off}}(Q)}4\ \le\ \mathrm{OPT}_{\mathrm{inv}}(Q)\ \le\ \mathrm{OPT}_{\mathrm{off}}(Q).\tag{16}
--   $$
--   It transfers the i.i.d. foresight lower bound to fixed populations (Theorem 1.2(iii)).
--
--   Differences from the source:
--   - encoding: known live multiset Q → a sequence Q : Fin T → Vec n; reason: both sides depend only on its multiset
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §5.3, p.13, eq. (16)

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_OPToff
import Definitions.Def_AvgValueAlloc_OPTinvQ

namespace AvgValueAlloc

/-- **(16): the inventory-known causal optimum is within factor four of offline welfare.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §5.3, p.13: "For a known live multiset Q, the inventory-known
causal optimum satisfies OPT_off(Q)/4 ≤ OPT_inv(Q) ≤ OPT_off(Q). (16)"

For thresholds `ρ > 0` and every live sequence `Q`: `OPT_off(Q)/4 ≤ OPT_inv(Q) ≤ OPT_off(Q)`,
where `OPT_inv(Q)` is the best causal welfare from zero surplus when `Q`'s multiset is known and
its items arrive in uniform order. -/
theorem eq_16 {n T : ℕ} (ρ : Fin n → ℚ) (hρ : ∀ j, 0 < ρ j) (Q : Fin T → Vec n) :
    OPToff ρ Q / 4 ≤ OPTinvQ ρ Q ∧ OPTinvQ ρ Q ≤ OPToff ρ Q := by sorry

end AvgValueAlloc
