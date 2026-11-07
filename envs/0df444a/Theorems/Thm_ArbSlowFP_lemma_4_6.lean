-- Prove2me | Theorems.Thm_ArbSlowFP_lemma_4_6
-- name    : ArbSlowFP.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:46:46.10929+00:00
-- url     : https://prove2.me/theorems/4c154251-04a6-409e-a1e1-394a20dbd6b7
-- title:
--   Lemma 4.6 — a rational bias realizes a priority rule
-- statement:
--   Let $A\in\mathbb Q^{m\times m}$ be skew-symmetric, let $f\in\mathbb Q^m$, and fix a total priority order. There is $\beta\in\mathbb Q^m$ such that the process $(6)$ initialized at $u_0=f+\beta$ has a unique maximizer at every decision time and follows exactly the fixed-priority trajectory from $f$.
--
--   This removes all ties from the clock's trajectory.
--
--   **Formalization Note** The fixed-priority trajectory is any sequence satisfying the priority process from $f$; there is exactly one such sequence. The conclusion is that its action at time $t$ is the unique maximizer of the $(f+\beta)$-process score after the same plays, for every $t$.
--
--   Differences from the source:
--   - encoding: a total priority order ≺ → an injective rank function, lower rank first; reason: same orders; a finite total order is an injective rank
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), p.29, Lemma 4.6

import Mathlib
import Definitions.Def_ArbSlowFP_ValidFrom

open Matrix

namespace ArbSlowFP

/-- Lemma 4.6, p.29 (arXiv:2610.08768, version of November 3, 2026, sha256 977c34b6…): for skew-symmetric
`A ∈ ℚ^{m×m}`, `f ∈ ℚ^m` and a priority, there is a rational `β` such that the process (6) from `f + β`
has a unique maximizer at every decision time and follows exactly the fixed-priority trajectory from
`f`.

**Formalization Note.** `∀ i, IsPriorityRun A rank f i → …` names the fixed-priority trajectory from
`f`; since a maximizer with least rank is unique, there is exactly one such `i`. A process with a unique
maximizer at every time has only one run, so the conclusion says that `i` is that run. The priority is
quantified before `β`. -/
theorem lemma_4_6 {ι : Type*} [Fintype ι] [Nonempty ι] (A : Matrix ι ι ℚ) (hA : Aᵀ = -A)
    (f : ι → ℚ) (rank : ι → ℕ) (hrank : Function.Injective rank) :
    ∃ β : ι → ℚ, ∀ i : ℕ → ι, IsPriorityRun A rank f i →
      ∀ t, IsUniqueMax (procScore A (f + β) i t) (i t) := by sorry

end ArbSlowFP
