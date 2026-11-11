-- Prove2me | Theorems.Thm_CubicPermFPRAS_lemma_49
-- name    : CubicPermFPRAS.lemma_49
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:59:04.760016+00:00
-- url     : https://prove2.me/theorems/8e0d345d-bce9-413d-93c8-243503a83201
-- title:
--   Lemma 49, p.53 — sampler with error $\eta$ in time $C_\alpha n^2\log^4(n/\eta)$
-- statement:
--   For every $\alpha>1$ there are constants for the sampler and $C_\alpha>0$ such that, for every $n\ge1$, positive activities $\lambda$, anchor $r$, $\alpha$-rough anchor weights $w(r,\cdot)$ and $0<\eta<1/4$, the sampler outputs a perfect matching whose law $\hat\mu$ satisfies
--   $$\|\hat\mu-\mu\|_{\mathrm{TV}}\le\eta,$$
--   where $\mu(M)=\lambda(M)/\lambda(\mathcal P)$, and on every tape it uses at most $C_\alpha n^2\log^4(n/\eta)$ operations, including its preprocessing.
--
--   Differences from the source:
--   - generalization: temperatures $\lambda_i$ of the cooling schedule (7) → arbitrary positive activities $\lambda$; reason: p.37: "The proofs of Lemmas 8 and 49 apply to arbitrary strictly positive edge activities"; the temperatures are instances
--   - generalization: "there is a randomized algorithm" → the defined sampler of the proof (pp.53–54), with its constants quantified after $\alpha$; reason: the defined sampler witnesses the existential
--   - encoding: $\|\hat\mu-\mu\|_{\mathrm{TV}}=\frac12\sum|\hat\mu-\mu|$; running time → `MarkovMixing.tvDist` (supremum over events); the charged cost on every tape; reason: the two forms of total variation agree for probability vectors; time is counted at unit cost per operation
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), Lemma 49, p.53 (PDF 55); proof, pp.53–54 (PDF 55–56)

import Mathlib
import Definitions.Def_CubicPermFPRAS_sampler
import Definitions.Def_mm_mixing

set_option autoImplicit false

namespace CubicPermFPRAS

/-- **Lemma 49** (perfect-matching sampler with adjustable error), p.53 (PDF 55), X. Chen, H. Guo, E. Vigoda, X. Yang, *An Õ(n³)-time FPRAS for the Permanent*, arXiv:2609.20717 (held version, sha256 9e14f335…).

For all `α > 1`, there exists a constant `C_α > 0` such that, given `α`-rough hole weights
`w(r,v)` at the activities `λ` for all `v ∈ V₂` and `0 < η < 1/4`, the sampler outputs, in
`C_α n² log⁴(n/η)` time, a perfect matching from a distribution `µ̂` with
`‖µ̂ − µ‖_TV ≤ η`, where `µ` is the `λ`-weighted distribution on `P`.

**Formalization Note.** "There is a randomized algorithm" is the defined `sampler` (proof,
pp.53–54) with constants `prm` quantified after `α`; the time is its charged cost on every
tape, including the preprocessing. Stated for arbitrary positive activities (p.37: "The proofs
of Lemmas 8 and 49 apply to arbitrary strictly positive edge activities"). `‖·‖_TV` is
`MarkovMixing.tvDist`, which equals `½∑|·|` (p.5) for probability vectors. -/
theorem lemma_49 : ∀ α : ℝ, 1 < α → ∃ (prm : SamplerParams) (C : ℝ), 0 < C ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ (lam : Matrix (Fin n) (Fin n) ℝ), (∀ u v, 0 < lam u v) →
    ∀ (r : Fin n) (w : Fin n → ℝ), IsRoughAnchor α lam r w →
    ∀ η : ℝ, 0 < η → η < 1 / 4 →
      MarkovMixing.tvDist (lawOf (sampler prm lam w η)) (muPM lam) ≤ η ∧
      ∀ ω : Tape, ((runFree (sampler prm lam w η) ω).2 : ℝ) ≤
        C * (n : ℝ) ^ 2 * Real.log (n / η) ^ 4 := by sorry

end CubicPermFPRAS
