-- Prove2me | Theorems.Thm_CausalFailureRank_truncated_controller
-- name    : CausalFailureRank.truncated_controller
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:15:50.786049+00:00
-- url     : https://prove2.me/theorems/66a9078f-98b2-4453-a36a-990bd44e7811
-- title:
--   App. B.5 — truncated controller under the certificate
-- statement:
--   Let $0<\delta\le1/2$ and let the caps satisfy the certificate (24), (25). The controller truncated at $\hat Q$, started at $r=\delta/2$, runs under immediate execution with failure probability at most $\delta$, and on every sample its bill is at most that of the uncapped reference controller. Moreover the larger contract class has the smaller value: $V_{\text{delayed}}(\delta)\le V_{\text{immediate}}(\delta)$.
--
--   This proves the upper bound in Theorem 3.1 under the stated certificate.
--
--   Differences from the source:
--   - generalization: one contract $I$ → the two execution classes, with their comparison added; reason: the source’s lower comparison and upper controllers use the two classes; the added clause connects them
--   - reading: "integers $\bar M_i\ge M_i$, $\bar L_i\ge L_i$ obtained by comparing … with integer powers of two" → every admissible integers; reason: every printed choice is admissible
--   - encoding: stages $1,\dots,N+1$ → 0-based stages, terminal $i\ge N$; reason: Lean indexing; no instance changes
--   - generalization: rational probabilities, fees and risk parameters → real ones; reason: rationality serves only computability, which is not claimed here; the rational case is an instance
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.5, eq. (25), p.19

import Mathlib
import Definitions.Def_CausalFailureRank_V
import Definitions.Def_CausalFailureRank_Qualifies
import Definitions.Def_CausalFailureRank_refController

open Filter Topology MeasureTheory

namespace CausalFailureRank

variable {N q : ℕ}

/-- **The truncated controller.** Zang, Li, Jin, Xu, *Causal Failure Rank Determines Statistical Depth*, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.5, p.19: "If a test exhausts Q̂_i without stopping, abandon
the entire task. A union bound adds at most δ/2 overflow risk to the reference risk δ/2. Couple the
actual and reference policies on the same observation tapes: until the first overflow they coincide,
and then the actual policy stops and deletes only future nonnegative charges. Its pathwise cost is thus
at most the reference cost, including every correction already executed on a path that ultimately
fails."

**Formalization Note.** Under the certificate (24), (25), at `r = δ/2` and `0 < δ ≤ 1/2`: the risk bound in
the original caps, and the pathwise comparison with the uncapped reference run. The last clause compares
the contracts: atomic commit-and-execute is simulated by commit then execute, so
`V current ≤ V currentPay`. -/
theorem truncated_controller (I : Instance N q) (sel : Fin N → Finset (Fin q) → Option (Fin q))
    (hsel : IsBadChildSelection I sel) (caps : Caps N) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (Mbar Lbar : Fin N → ℕ) (hML : ∀ i, Mbound I i ≤ Mbar i ∧ Lbound I i ≤ Lbar i)
    (hQ : ∀ i, (Qhat I δ Mbar Lbar i : ℕ∞) ≤ caps.Q i)
    (hH : ((∑ i, I.normalCalls i + ∑ i, Qhat I δ Mbar Lbar i + min N q : ℕ) : ℕ∞) ≤ caps.H) :
    tapeLaw I {ω | ¬ SuccessFrom I .currentPay caps
      (refAction I sel (some (Qhat I δ Mbar Lbar)) 0 Finset.univ (δ / 2)) (initState I) ω} ≤
        ENNReal.ofReal δ ∧
    (∀ ω, billFrom I .currentPay caps
        (refAction I sel (some (Qhat I δ Mbar Lbar)) 0 Finset.univ (δ / 2)) (initState I) ω ≤
      billFrom I .currentPay (noCaps N) (refAction I sel none 0 Finset.univ (δ / 2)) (initState I) ω) ∧
    V I .current caps δ ≤ V I .currentPay caps δ := by sorry

end CausalFailureRank
