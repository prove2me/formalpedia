-- Prove2me | Theorems.Thm_FairReplay_Supplement_eq_57
-- name    : FairReplay.Supplement.eq_57
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:58:00.986584+00:00
-- url     : https://prove2.me/theorems/96237bcf-7ed9-41b8-8eee-800f33320592
-- title:
--   Theorem 10.6, eq. (57) — $Q^{\mathrm{rounds}}_{\mathrm{suite}}=\Theta(\log(1/\delta)/d)$, $Q^{\mathrm{exec}}_{\mathrm{suite}}=\Theta(n_+\log(1/\delta)/d)$
-- statement:
--   For a fixed graph $H$ with at least one edge, fixed $p,s>0$ with $p+s<1$ and fixed $\delta\in(0,1/2)$, as $d\to0$,
--   $$Q^{\mathrm{rounds}}_{\mathrm{suite}}=\Theta\Big(\frac{\log(1/\delta)}{d}\Big),\qquad Q^{\mathrm{exec}}_{\mathrm{suite}}=\Theta\Big(\frac{n_+\log(1/\delta)}{d}\Big),$$
--   where $Q^{\mathrm{rounds}}_{\mathrm{suite}}$ is the optimal null expected number of suite rounds of $\delta$-correct testers and $Q^{\mathrm{exec}}_{\mathrm{suite}}=2n_+Q^{\mathrm{rounds}}_{\mathrm{suite}}$ the corresponding number of program executions.
--
--   Differences from the source:
--   - encoding: Q (no displayed definition) → the infimum in [0, ∞] of the null expected stopping time over δ-correct testers; reason: the paper's own usage ("optimal expected null declared cost", p.20); the reading of the published Theorem 10.4
--   - encoding: Θ(·) as d → 0 with the other parameters fixed → ∃ c, C, d₀ > 0 chosen before d (depending only on the fixed parameters) with c·X ≤ Q ≤ C·X for d ∈ (0, d₀); d₀ inside the theorem's domain; reason: the reading of the published Theorem 10.4, eq. (37)
-- source:
--   Sah, Zhang, Lian, Testing Fairness of Evolving Software under Uncertainty, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0a0f5960aedaf6aba60adc41e966efc604b6379b3180b06590610d025), Theorem 10.6, eq. (57), p.17 (PDF p.19)

import Mathlib
import Definitions.Def_FairReplay_Supplement_activeVertices
import Definitions.Def_FairReplay_Supplement_Qsuite

namespace FairReplay.Supplement

/-- **Theorem 10.6, eq. (57), the suite Θ rates** (Sah, Zhang, Lian, *Testing Fairness of Evolving Software under Uncertainty*, STOC 2027 submission (manuscript of 2026-11-03, sha256 e23940a0…), Theorem 10.6, eq. (57), p.17 (PDF p.19)):
"Consequently, for fixed interior p, s, r, Q^rounds_suite = Θ(log(1/δ)/d), Q^exec_suite =
Θ(n+ log(1/δ)/d) (57) as d → 0 with δ, the graph, and hence n+ fixed."

For a fixed graph `H` with at least one edge, fixed `p, s > 0` with `p + s < 1` and fixed `δ ∈ (0, 1/2)`,
there are `c, C, d₀ > 0` (chosen before `d`) such that for every `d ∈ (0, d₀)`:
`c log(1/δ)/d ≤ Q^rounds_suite ≤ C log(1/δ)/d` and `c n+ log(1/δ)/d ≤ Q^exec_suite ≤ C n+ log(1/δ)/d`,
with `n+ = |V+(H)|`.

**Formalization Note** `Q^rounds_suite` is the infimum, in `[0, ∞]`, of the null expected number of suite
rounds over testers δ-correct against every single-changed-endpoint alternative, and
`Q^exec_suite = 2 n+ Q^rounds_suite`. The constants may depend on `p, s, δ` and `H`. -/
theorem eq_57 {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hE : 1 ≤ H.edgeFinset.card) (p s δ : ℝ) (hp : 0 < p) (hs : 0 < s) (hps : p + s < 1)
    (hδ : 0 < δ) (hδ2 : δ < 1 / 2) :
    ∃ c C d₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < d₀ ∧ d₀ ≤ 1 - p - s ∧
      ∀ d : ℝ, 0 < d → d < d₀ →
        ENNReal.ofReal (c * Real.log (1 / δ) / d) ≤ QsuiteRounds H p s d δ ∧
        QsuiteRounds H p s d δ ≤ ENNReal.ofReal (C * Real.log (1 / δ) / d) ∧
        ENNReal.ofReal (c * (activeVertices H).card * Real.log (1 / δ) / d) ≤
          QsuiteExec H p s d δ ∧
        QsuiteExec H p s d δ ≤
          ENNReal.ofReal (C * (activeVertices H).card * Real.log (1 / δ) / d) := by sorry

end FairReplay.Supplement
