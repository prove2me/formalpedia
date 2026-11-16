-- Prove2me | Theorems.Thm_CondGeoVerif_Supplement_theorem_D_2
-- name    : CondGeoVerif.Supplement.theorem_D_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:15:16.7302+00:00
-- url     : https://prove2.me/theorems/6b2cb3bc-8bab-4473-8f97-4bb77c6f98bc
-- title:
--   Theorem D.2 — the conditional moment threshold: $J_\eta$ has a unique zero $\eta^\dagger$, and $1/2<4\Phi(A)-3<a^\dagger<a_c<1$
-- statement:
--   For $0<\eta<1/2$ let $M_\eta(u)$ be the signed conditional moment problem (D.1), $F_\eta(u)=2M_\eta(u)-\bar\Phi(u)$ and
--   $$J_\eta=\int_0^\infty F_\eta(u)\,du.\qquad(D.6)$$
--   There is a unique $\eta^\dagger\in(0,1/2)$ with $J_{\eta^\dagger}=0$. Set $a^\dagger=1-2\eta^\dagger$. Then $J_\eta<0$ for $\eta<\eta^\dagger$ and $J_\eta>0$ for $\eta>\eta^\dagger$. The constants satisfy
--   $$\frac12<4\Phi(A)-3<a^\dagger<a_c=2\Phi(A)-1<1,\qquad A=\sqrt{2\log2}.\qquad(D.8)$$
--   In particular $\eta^\dagger<1/4$.
--
--   The threshold $a^\dagger$ separates the signal levels at which halfspaces admit the square-root verification of Theorem G.1.
--
--   Differences from the source:
--   - encoding: J_η < 0 for η < η†, J_η > 0 for η > η† → for 0 < η < η† and for η† < η < 1/2; reason: (D.1) is defined for 0 < η < 1/2 only
--   - encoding: M_η(u) of (D.1) → the published first-moment program Mprog 1 η in dimension one with disagreement 1{z₁ < −u}; reason: same supremum over Borel allocations with values in [0, 1]
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), Theorem D.2 and (D.6)–(D.8), p.39 (PDF p.42); proof pp.39–40

import Mathlib
import Definitions.Def_CondGeoVerif_Supplement_Mhalf

set_option autoImplicit false

open MeasureTheory Cohen2019.Robust

namespace CondGeoVerif.Supplement

/-- **Theorem D.2 (The conditional moment threshold)** (Chen, *The Conditional Geometry of
Statistical Verification*, manuscript, October 2026, sha256 07a66d18…, p.39 = PDF p.42). There is a
unique `η† ∈ (0, 1/2)` with `J_{η†} = 0`. Set `a† = 1 − 2η†`. Then `J_η < 0` for `η < η†` and
`J_η > 0` for `η > η†`. The constants satisfy
`1/2 < 4Φ(A) − 3 < a† < a_c = 2Φ(A) − 1 < 1`, `A = √(2 log 2)` (D.8). In particular `η† < 1/4`.

**Formalization Note** `J_η = ∫₀^∞ (2M_η(u) − Φ̄(u)) du` with `M_η` the signed conditional moment
problem (D.1) (`Jeta`). The sign claims range over `0 < η < 1/2`, the range on which (D.1) is
defined. `a_c` is `aC = 2Φ(A) − 1` by definition. -/
theorem theorem_D_2 :
    ∃ ηd : ℝ, 0 < ηd ∧ ηd < 1 / 2 ∧ Jeta ηd = 0 ∧
      (∀ η : ℝ, 0 < η → η < 1 / 2 → Jeta η = 0 → η = ηd) ∧
      (∀ η : ℝ, 0 < η → η < ηd → Jeta η < 0) ∧
      (∀ η : ℝ, ηd < η → η < 1 / 2 → 0 < Jeta η) ∧
      1 / 2 < 4 * Phi critA - 3 ∧ 4 * Phi critA - 3 < 1 - 2 * ηd ∧ 1 - 2 * ηd < aC ∧
      aC = 2 * Phi critA - 1 ∧ aC < 1 ∧ ηd < 1 / 4 := by sorry

end CondGeoVerif.Supplement
