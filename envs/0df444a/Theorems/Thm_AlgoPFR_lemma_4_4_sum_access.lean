-- Prove2me | Theorems.Thm_AlgoPFR_lemma_4_4_sum_access
-- name    : AlgoPFR.lemma_4_4_sum_access
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:44:27.002208+00:00
-- url     : https://prove2.me/theorems/4f05670a-7609-4e1f-81a2-8e2088af22ee
-- title:
--   Lemma 4.4 — access to $X+Y$ with envelope $M_Y$
-- statement:
--   Suppose we have algorithmic access to $X,Y$ with envelopes $M_X,M_Y$. The sum protocol gives algorithmic access to $X+Y$ with envelope $M_Y$ and slack
--   $$\Delta[X+Y]\le\Delta[Y]+2\,d[X;Y].$$
--   Its sampler makes two parent calls, and its coin makes two.
--
--   Sums are the operations with no rejection, so their cost shows up only through the slack.
--
--   Differences from the source:
--
--   - reading: "algorithmic access" of Definition 4.1, including expected poly(n, K) time → the sampler law, the coin rate and the envelope, with parent-call counts in place of time; reason: Definition 4.1's time clause fails for the protocols of Lemma 4.5 on rare labels, and the source tracks costs by parent calls
--   - generalization: no call counts in the printed statement → the sampler and the coin each make exactly two parent calls; reason: read off the printed proof, and used by its cost recursion; the printed claim follows by dropping these clauses
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Lemma 4.4, p.20

import Mathlib
import Definitions.Def_AlgoPFR_Protocols

set_option autoImplicit false

open scoped ENNReal Pointwise

namespace AlgoPFR

/-- **Lemma 4.4.** Arunachalam, Dutt, Grewal, Gupte, *Marton's conjecture in polynomial time*, arXiv:2609.20771 (sha256 60e45066…), p.20: from algorithmic access to `X, Y` the sum protocol gives algorithmic
access to `X + Y` with envelope `M_Y` and slack `Δ[X + Y] ≤ Δ[Y] + 2 d[X;Y]`.

**Formalization Note.** The protocol is `sumOracle`, built from the two parents as black boxes. Its
call counts are read off the proof: the sampler makes two parent calls and the coin makes two. -/
theorem lemma_4_4_sum_access {n : ℕ} (X Y : Oracle n) (MX MY : ℝ) (hX : IsAccess X MX)
    (hY : IsAccess Y MY) :
    (sumOracle X Y).sample = sumLaw X.sample Y.sample ∧
      IsAccess (sumOracle X Y) MY ∧
      slack (sumOracle X Y) MY ≤ slack Y MY + 2 * rd X.sample Y.sample ∧
      (sumSampleProc X Y).UsesCalls 2 ∧ ∀ z, (sumCoinProc X Y z).UsesCalls 2 := by sorry

end AlgoPFR
