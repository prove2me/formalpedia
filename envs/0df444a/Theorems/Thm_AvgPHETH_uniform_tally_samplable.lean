-- Prove2me | Theorems.Thm_AvgPHETH_uniform_tally_samplable
-- name    : AvgPHETH.uniform_tally_samplable
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:31:41.76134+00:00
-- url     : https://prove2.me/theorems/d06fa2ce-aca8-4acc-9848-f1d68bfe2a2a
-- title:
--   Footnote 2 — $\mathcal U$ and $\mathcal T$ are samplable without $O$
-- statement:
--   The uniform family $\mathcal U$ and the tally family $\mathcal T$ are samplable without $O$: there is one machine that is a sampler of $\mathcal U$ with every oracle, and one that is a sampler of $\mathcal T$ with every oracle.
--
--   Consequently $\mathrm{Dist}\Sigma_d^{p,O}\subseteq\mathrm{AvgP}^O$ implies $\Sigma_d^{p,O}\times\{\mathcal U,\mathcal T\}\subseteq\mathrm{AvgP}^O$, the form of the hypothesis that the proofs use.
--
--   Differences from the source:
--   - encoding: a randomized polynomial-time algorithm → a deterministic machine reading $r(n)$ uniform coins as a second input; reason: the same sampled distributions for an exact sampler with a polynomial time bound
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), footnote 2, p.10 (PDF 12)

import Mathlib
import Definitions.Def_AvgPHETH_IsSampler
import Definitions.Def_AvgPHETH_uniformDist
import Definitions.Def_AvgPHETH_tallyDist
open KarpLiptonOM

namespace AvgPHETH

/-- The uniform and tally families are samplable without `O` (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), footnote 2, p.10 (PDF 12)): one machine
samples `U` with every oracle, and one machine samples `T` with every oracle. In particular
`DistΣ_d^{p,O} ⊆ AvgP^O` implies `Σ_d^{p,O} × {U, T} ⊆ AvgP^O`. -/
theorem uniform_tally_samplable :
    (∃ (M : OracleTM) (r : Polynomial ℕ) (e : ℕ), ∀ O, IsSampler M r e O uniformDist) ∧
    (∃ (M : OracleTM) (r : Polynomial ℕ) (e : ℕ), ∀ O, IsSampler M r e O tallyDist) := by sorry

end AvgPHETH
