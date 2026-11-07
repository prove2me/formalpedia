-- Prove2me | Theorems.Thm_ChoresEFX_theorem_3_3
-- name    : ChoresEFX.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:08:39.751692+00:00
-- url     : https://prove2.me/theorems/1608e6b1-b115-473f-9084-b34f2c7a019e
-- title:
--   Theorem 3.3 — MFCP invokes maximum flow at most $1+\lceil n^2\log(\hat C_{\max}/\hat C_{\min})/(t\log(1+t))\rceil$ times
-- statement:
--   Let $\hat C>0$, $\hat C_{\max}=\max_{i,g}\hat C_i(g)$ and $\hat C_{\min}=\min_{i,g}\hat C_i(g)$, with $0<t\le1/100$, $0<\beta<1$ and $m\beta>n$. Every run of Algorithm 2 with $J$ failed rounds satisfies
--
--   $$J+1\le1+\left\lceil\frac{n^2\log(\hat C_{\max}/\hat C_{\min})}{t\log(1+t)}\right\rceil,$$
--
--   where $J+1$ is the number of maximum-flow invocations. Each reached weight vector has a water level and a maximum flow, and the algorithm has an output.
--
--   The bound gives termination, and together with the bit-length argument it makes MFCP polynomial.
--
--   Differences from the source:
--   - reading: the number of times Algorithm 2 invokes a maximum-flow algorithm is at most (5) → every partial run with J failed rounds has J + 1 at most the bound; each reached weight vector has a next round; an output exists; reason: a run with J failed rounds makes one more invocation, and the two added clauses are the page's "MFCP must eventually find a full flow"
--   - generalization: n ≥ 2 agents (standing, §2, p.5) → n ≥ 1 ([Nonempty ι]); reason: the argument does not use n ≥ 2, and the statement specializes to n ≥ 2
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cf…), Theorem 3.3, p.9

import Mathlib
import Definitions.Def_ChoresEFX_IsMfcpOutput

namespace ChoresEFX

/-- **Theorem 3.3**, p.9.

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC 2027
submission (manuscript sha256 b26d14cf…).

With `Ĉ_max = max_{i,g} Ĉ_i(g)` and `Ĉ_min = min_{i,g} Ĉ_i(g) > 0`, the number of times Algorithm 2
invokes a maximum-flow algorithm is at most `1 + ⌈n² log(Ĉ_max/Ĉ_min) / (t log(1 + t))⌉` (5).

**Formalization Note.** A run with `J` failed rounds has made `J` invocations and makes at least one more,
so the count is `J + 1`. For the bound to be about a loop that really goes on, the statement also says that
each reached weight vector has a water level and a maximum flow, and that an output exists. The logarithm is
natural; the ratio of two logarithms does not depend on the base. -/
theorem theorem_3_3 {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (C : ι → κ → ℝ) (hC : ∀ i g, 0 < C i g) (t β : ℝ) (ht : 0 < t) (ht' : t ≤ 1 / 100)
    (hβ : 0 < β) (hβ' : β < 1) (hmβ : (Fintype.card ι : ℝ) < (Fintype.card κ : ℝ) * β) :
    (∀ (J : ℕ) (v : ℕ → ι → ℝ), IsFailedRun C t β J v →
      J + 1 ≤ 1 + ⌈(Fintype.card ι : ℝ) ^ 2 * Real.log (maxCost C / minCost C) /
        (t * Real.log (1 + t))⌉₊) ∧
    (∀ (J : ℕ) (v : ℕ → ι → ℝ), IsFailedRun C t β J v →
      ∃ s f, IsWaterLevel C β (v J) s ∧ IsMaximumFlow C t β (v J) s f) ∧
    (∃ p γ w, IsMfcpOutput C t β p γ w) := by sorry

end ChoresEFX
