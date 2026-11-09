-- Prove2me | Theorems.Thm_CommThresholdPR_StrongConverse_proposition_7_2
-- name    : CommThresholdPR.StrongConverse.proposition_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:37.218463+00:00
-- url     : https://prove2.me/theorems/dac3e5d0-0123-4984-84ed-c2a1a5ac0e6d
-- title:
--   Proposition 7.2 — positivity below threshold and the unconditional zero-rate identity
-- statement:
--   For every total relation on nonempty finite alphabets and arbitrary joint input law $\mu$,
--   $$0\le R<\operatorname{IC}_{\mu}(g,0)\ \Longrightarrow\ \operatorname{err}_{\mu}(R)>0,$$
--   and, independently of the existence of a rate below threshold,
--   $$\operatorname{err}_{\mu}(0)=\eta=1-\omega(g,\mu).$$
--   The value $\omega$ is the optimum over deterministic local output maps without communication. The second assertion is unconditional in the standing model. These facts identify the positive error gap needed in the explicit exponents.
--
--   Differences from the source:
--   - encoding: finite public randomness and independent finite private random tapes → finite public seeds and private local kernels on finite binary trees; reason: finite contingent choice tables realize the kernels as independent private tapes; posterior local tape laws recover every source transcript/output law and cost without any uniform bound
--   - encoding: operational infima on nonempty sets bounded below by zero → a guarded real infimum over the entire protocol type; reason: on the source domain input exchange and zero-message protocols ensure nonemptiness and finite information is nonnegative; the fallback is only outside that domain, with these facts left to solvers
-- source:
--   Daiki Suruga, The Exact Communication Threshold for Parallel Repetition, STOC 2027 submission #304 (October 2026), Proposition 7.2, p. 23, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/304.pdf

import Definitions.Def_CommThresholdPR_StrongConverse_Simulation

namespace CommThresholdPR.StrongConverse

variable {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Nonempty X] [Nonempty Y] [Nonempty A] [Nonempty B]
theorem proposition_7_2 (g : TotalRelation X Y A B) (μ : PMF (X × Y)) :
    (∀ R : ℝ, 0 ≤ R → R < informationComplexity g μ 0 → 0 < errorAtRate g μ R) ∧
    errorAtRate g μ 0 = gap g μ := by sorry

end CommThresholdPR.StrongConverse
