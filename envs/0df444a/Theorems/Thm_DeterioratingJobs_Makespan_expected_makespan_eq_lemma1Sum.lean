-- Prove2me | Theorems.Thm_DeterioratingJobs_Makespan_expected_makespan_eq_lemma1Sum
-- name    : DeterioratingJobs.Makespan.expected_makespan_eq_lemma1Sum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:08:15.56157+00:00
-- url     : https://prove2.me/theorems/9f7bc6bf-53f6-43cc-bc67-857f6a471311
-- title:
--   Section 1, after Eq. (2) — $\mathrm E\,S_N(\pi)$ is the sum (1) with $\mu_i=\mathrm E(X_i)$, $\gamma_i=1+\alpha_i$
-- statement:
--   In the linear deterioration model on a probability space $(\Omega,\mathcal F,P)$, suppose every initial processing requirement $X_i$ is integrable. Then for every schedule $\pi$ the expected makespan is
--
--   $$
--   \mathrm E\, S_N(\pi) = \sum_{i=1}^{N} \mathrm E\bigl(X_{\pi(i)}\bigr) \prod_{r=i+1}^{N} \bigl(1+\alpha_{\pi(r)}\bigr),
--   $$
--
--   that is, the sum (1) of Lemma 1 with $\mu_i=\mathrm E(X_i)$ and $\gamma_i=1+\alpha_i$.
--
--   This is the "identification of the proper terms in Lemma 1" that the paper makes after (2): it reduces the expected makespan to a deterministic objective to which Lemma 1 applies.
--
--   **Formalization Note** Expectations are Bochner integrals; integrability of each $X_i$ is assumed (without it the integral is $0$ by convention). No independence and no sign condition on $X_i$ or $\alpha_i$ is needed. Positions are 0-based.
-- source:
--   Browne, Yechiali, Scheduling Deteriorating Jobs on a Single Processor, Oper. Res. 38 (1990), p. 496, Section 1, the sentence after Eq. (2) (identification of the proper terms in Lemma 1)

import Mathlib
import Definitions.Def_DeterioratingJobs_Makespan_InterchangeSum
import Definitions.Def_DeterioratingJobs_Makespan_Model

namespace DeterioratingJobs.Makespan

open MeasureTheory

/-- Section 1, after Eq. (2) (Browne–Yechiali 1990, p. 496): the expected makespan has the form (1)
of Lemma 1 with `μ_i = E(X_i)` and `γ_i = 1 + α_i`:
`E S_N(π) = ∑_i E(X_{π(i)}) ∏_{r>i} (1 + α_{π(r)})`. -/
theorem expected_makespan_eq_lemma1Sum {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (X : Fin N → Ω → ℝ) (hX : ∀ i, Integrable (X i) P)
    (α : Fin N → ℝ) (π : Equiv.Perm (Fin N)) :
    expectedMakespan P X α π =
      lemma1Sum (fun i => ∫ ω, X i ω ∂P) (fun i => 1 + α i) π := by sorry

end DeterioratingJobs.Makespan
