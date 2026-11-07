-- Prove2me | Theorems.Thm_AvgValueAlloc_appendix_A1_horizon
-- name    : AvgValueAlloc.appendix_A1_horizon
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:40:15.743621+00:00
-- url     : https://prove2.me/theorems/575eff84-80d8-4596-9a8f-9a20cd21f457
-- title:
--   Appendix A.1 — causal horizon comparison $\mathrm{OPT}_{\mathrm{on}}(D,h)\ge\frac{h(h-1)}{2T(T-1)}\mathrm{OPT}_{\mathrm{on}}(D,T)$
-- statement:
--   Let $\rho\in\mathbb Q^n_{>0}$, $D$ a finite law and $2\le h\le T$. Then
--   $$
--   \mathrm{OPT}_{\mathrm{on}}(D,h)\ \ge\ \frac{h(h-1)}{2T(T-1)}\,\mathrm{OPT}_{\mathrm{on}}(D,T).
--   $$
--   The law-known causal optimum on a shorter horizon keeps a fixed fraction of the full-horizon optimum; this is what proves (7) without an expected-type-count floor.
--
--   Differences from the source: none.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), Appendix A.1, pp.13–14

import Mathlib
import Definitions.Def_AvgValueAlloc_FinLaw
import Definitions.Def_AvgValueAlloc_OPTon

namespace AvgValueAlloc

open scoped ENNReal

/-- **Appendix A.1: causal horizon comparison.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), Appendix A.1, pp.13–14: "For 2 ≤ h ≤ T, hide h real i.i.d.
arrivals in a uniform h-subset of T positions and draw D-values elsewhere. Keep only real items with
real anchors: each remaining bundle is affordable after its anchor. Singleton/pair survival is h/T
and h(h − 1)/[T(T − 1)], giving OPT_on(D, h) ≥ [h(h − 1)/(2T(T − 1))] OPT_on(D, T)."

For thresholds `ρ > 0`, every finite law `D` and `2 ≤ h ≤ T`:
`OPT_on(D, h) ≥ h(h − 1)/(2T(T − 1)) · OPT_on(D, T)`. -/
theorem appendix_A1_horizon {n : ℕ} (ρ : Fin n → ℚ) (hρ : ∀ j, 0 < ρ j) (D : FinLaw n)
    (hD : D.IsLaw) (h T : ℕ) (h2 : 2 ≤ h) (hhT : h ≤ T) :
    ENNReal.ofReal (((h : ℝ) * ((h : ℝ) - 1)) / (2 * (T : ℝ) * ((T : ℝ) - 1))) * OPTon ρ D T ≤
      OPTon ρ D h := by sorry

end AvgValueAlloc
