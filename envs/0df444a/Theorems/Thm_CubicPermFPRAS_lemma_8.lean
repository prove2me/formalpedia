-- Prove2me | Theorems.Thm_CubicPermFPRAS_lemma_8
-- name    : CubicPermFPRAS.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:58:43.246765+00:00
-- url     : https://prove2.me/theorems/11b3707b-9469-423d-b7fa-633a4ba98762
-- title:
--   Lemma 8, p.11 — sampler with error $1/16$ in time $C_\alpha n^2\log^3(2n)$ (corrected: $\log^3(2n)$ for $\log^3 n$)
-- statement:
--   For every fixed $\alpha>1$ there are constants for the sampler and $C_\alpha>0$ such that, for every $n\ge1$, positive activities $\lambda$, anchor $r$ and $\alpha$-rough anchor weights $w(r,\cdot)$, the sampler with error tolerance $1/16$ outputs a perfect matching whose law $\hat\mu$ satisfies
--   $$\|\hat\mu-\mu\|_{\mathrm{TV}}\le\frac1{16},$$
--   and on every tape it uses at most $C_\alpha n^2\log^3(2n)$ operations.
--
--   This sampler initializes every Phase-1 learning batch.
--
--   Differences from the source:
--   - correction: time $C_\alpha n^2\log^3 n$ → time $C_\alpha n^2\log^3(2n)$; reason: at $n=1$ the printed bound is $0$ while the sampler performs at least one operation (it charges at least $2$ for its preprocessing); the proof gives $O_\alpha(n^2\log^3(2n))$ (p.54), and for $n\ge2$, $\log(2n)\le2\log n$
--   - generalization: temperatures $\lambda_i$ of the cooling schedule (7) → arbitrary positive activities $\lambda$; reason: p.37: "The proofs of Lemmas 8 and 49 apply to arbitrary strictly positive edge activities"; the temperatures are instances
--   - generalization: "there is a randomized algorithm" → the defined sampler of the proof (pp.53–54), with its constants quantified after $\alpha$; reason: the defined sampler witnesses the existential
--   - encoding: $\|\hat\mu-\mu\|_{\mathrm{TV}}=\frac12\sum|\hat\mu-\mu|$; running time → `MarkovMixing.tvDist` (supremum over events); the charged cost on every tape; reason: the two forms of total variation agree for probability vectors; time is counted at unit cost per operation
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), Lemma 8, p.11 (PDF 13); proof, p.54 (PDF 56)

import Mathlib
import Definitions.Def_CubicPermFPRAS_sampler
import Definitions.Def_mm_mixing

set_option autoImplicit false

namespace CubicPermFPRAS

/-- **Lemma 8** (perfect-matching sampler), p.11 (PDF 13), X. Chen, H. Guo, E. Vigoda, X. Yang, *An Õ(n³)-time FPRAS for the Permanent*, arXiv:2609.20717 (held version, sha256 9e14f335…) (corrected: `log³(2n)` for
`log³ n`).

For every fixed `α > 1`, there exists a constant `C_α > 0` such that, given `α`-rough hole
weights `w(r,v)` at the activities `λ`, the sampler outputs, in time `C_α n² log³(2n)`, a perfect
matching with distribution `µ̂` satisfying `‖µ̂ − µ‖_TV ≤ 1/16`.

**Formalization Note.** The algorithm is the defined `sampler` with `η = 1/16` (p.54: "For
fixed `η = 1/16`, the sharper bound is `O_α(n² log³(2n))`"); its constants `prm` are quantified
after `α`. The printed `log³ n` is `0` at `n = 1`, where the sampler performs at least one
operation; the bound is stated with `log³(2n)`, which the proof gives (p.54). Stated for
arbitrary positive activities (p.37). -/
theorem lemma_8 : ∀ α : ℝ, 1 < α → ∃ (prm : SamplerParams) (C : ℝ), 0 < C ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ (lam : Matrix (Fin n) (Fin n) ℝ), (∀ u v, 0 < lam u v) →
    ∀ (r : Fin n) (w : Fin n → ℝ), IsRoughAnchor α lam r w →
      MarkovMixing.tvDist (lawOf (sampler prm lam w (1 / 16))) (muPM lam) ≤ 1 / 16 ∧
      ∀ ω : Tape, ((runFree (sampler prm lam w (1 / 16)) ω).2 : ℝ) ≤
        C * (n : ℝ) ^ 2 * Real.log (2 * n) ^ 3 := by sorry

end CubicPermFPRAS
