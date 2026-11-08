-- Prove2me | Theorems.Thm_CausalFailureRank_eq_19_monotone
-- name    : CausalFailureRank.eq_19_monotone
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:15:06.536663+00:00
-- url     : https://prove2.me/theorems/c748de94-a184-4f61-a5ac-bf56cee429d5
-- title:
--   Eqs. (19), (20) — monotonicity of the continuation values
-- statement:
--   For every stage $i$, unused tools $R$ and $\lambda>0$,
--   $$0\le G_g\le G_b\le\lambda,$$
--   where $G_g=G_{i+1,R}$ and $G_b$ is the cheapest legal error continuation, or $\lambda$ if no correction is available. This keeps the penalty $G_b-G_g$ passed to $J_i$ in range.
--
--   Differences from the source:
--   - encoding: stages $1,\dots,N+1$ → 0-based stages, terminal $i\ge N$; reason: Lean indexing; no instance changes
--   - generalization: rational probabilities, fees and risk parameters → real ones; reason: rationality serves only computability, which is not claimed here; the rational case is an instance
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.2, eqs. (19), (20), p.16

import Mathlib
import Definitions.Def_CausalFailureRank_G

open Filter Topology MeasureTheory

namespace CausalFailureRank

variable {N q : ℕ}

/-- **Monotonicity of the continuation values, (19)–(20).** Zang, Li, Jin, Xu, *Causal Failure Rank Determines Statistical Depth*, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.2, p.16: "Resource monotonicity
gives 0 ≤ G_g ≤ G_b ≤ λ."

**Formalization Note.** `G_g = G I (i+1) R λ`, and `G_b` is `Gb`. The paper's `λ > 0` is a hypothesis. -/
theorem eq_19_monotone (I : Instance N q) (i : Fin N) (R : Finset (Fin q)) (lam : ℝ) (hlam : 0 < lam) :
    0 ≤ G I (i.val + 1) R lam ∧ G I (i.val + 1) R lam ≤ Gb I i R lam ∧ Gb I i R lam ≤ lam := by sorry

end CausalFailureRank
