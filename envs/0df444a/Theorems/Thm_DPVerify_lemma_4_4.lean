-- Prove2me | Theorems.Thm_DPVerify_lemma_4_4
-- name    : DPVerify.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:54:05.166062+00:00
-- url     : https://prove2.me/theorems/f5d865fb-8a3c-420c-8235-488393fc2433
-- title:
--   Lemma 4.4 — $(\beta,\varepsilon,\delta)$-one-way perfect generalization gives a $4(\beta+2\varepsilon+\delta)$-replicable algorithm with the same output law
-- statement:
--   This is Theorem 3.17 of [BGH+23], as restated in the paper.
--
--   Let $\beta,\varepsilon,\delta\in(0,1)$, let $\mathcal A:\mathcal X^m\to\mathcal Y$ be a randomized algorithm with a finite output space, and let $D$ be a distribution on $\mathcal X$. If $\mathcal A$ satisfies the $(\beta,\varepsilon,\delta)$-one-way perfect generalization condition at $D$, then there is a randomized algorithm $\mathcal A'$ such that
--
--   1. $\mathcal A'(S)$ and $\mathcal A(S)$ have the same law for every sample $S$, and
--   2. $\mathcal A'$ is $4(\beta+2\varepsilon+\delta)$-replicable at $D$.
--
--   This is the last step of the transfer from differential privacy to replicability; Theorem 4.1 then uses the replicable algorithm $\mathcal A'$ in place of the verifier's message algorithm.
--
--   Differences from the source:
--   - generalization: $\mathcal A$ is $(\beta,\varepsilon,\delta)$-one-way perfectly generalizing (the condition at every distribution) → the condition at the given $D$ only; reason: the conclusion concerns $D$ alone; an algorithm satisfying the condition at every distribution satisfies it at $D$, so the printed lemma is the special case
--   - encoding: finite output space; identical output distribution → a finite type with its discrete σ-algebra; $\mathcal A'(S)$ and $\mathcal A(S)$ have the same law for every sample $S$; reason: Lean representation
--   - encoding: with probability at least $1-\beta$ over $S\sim D^m$ (Definition 2.4) → a measurable set of good samples of probability at least $1-\beta$; reason: for a finite output space the set of good samples is measurable, so the condition is the same
--   - encoding: an algorithm $\mathcal A:\mathcal X^m\to\mathcal Y$, a distribution $D$ → a randomized algorithm with explicit coins, jointly measurable, between measurable spaces; $D$ a probability measure; reason: Lean representation; makes every probability defined
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Lemma 4.4, p.18 (PDF p.21); Definitions 2.4–2.5, p.5 (PDF p.8)

import Mathlib
import Definitions.Def_DPVerify_RandAlg
import Definitions.Def_DPVerify_IsOWPGAt
import Definitions.Def_DPVerify_IsReplicableAt

set_option autoImplicit false

open MeasureTheory

namespace DPVerify

/-- Lemma 4.4 (Theorem 3.17 of [BGH+23], restated; Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), p.18 = PDF p.21): one-way perfect
generalization gives replicability. Let `β, ε, δ ∈ (0, 1)` and let `A : X^m → Y` have a finite
output space. If `A` satisfies the `(β, ε, δ)`-one-way perfect generalization condition at `D`,
then there is an algorithm `A′` with the same output law as `A` on every sample that is
`4(β + 2ε + δ)`-replicable at `D`.

**Formalization Note** The hypothesis is the OWPG condition at `D` only (the printed lemma assumes
it at every distribution), and `A′` may depend on `D`, as printed ("for any distribution `D` …
there exists an algorithm `A′`"). "Identical output distribution" is `A′.law S = A.law S` for every
sample `S`. The finite output space carries its discrete σ-algebra. -/
theorem lemma_4_4 (X Y : Type) [MeasurableSpace X] [Fintype Y] [MeasurableSpace Y]
    [DiscreteMeasurableSpace Y] (m : ℕ) (β ε δ : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) (hε0 : 0 < ε)
    (hε1 : ε < 1) (hδ0 : 0 < δ) (hδ1 : δ < 1) (A : RandAlg X Y m) (D : ProbabilityMeasure X)
    (h : IsOWPGAt A D β ε δ) :
    ∃ A' : RandAlg X Y m, (∀ S, A'.law S = A.law S) ∧
      IsReplicableAt A' D (4 * (β + 2 * ε + δ)) := by sorry

end DPVerify
