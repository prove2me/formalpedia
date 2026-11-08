-- Prove2me | Theorems.Thm_CausalFailureRank_sprt_bound
-- name    : CausalFailureRank.sprt_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:14:15.370645+00:00
-- url     : https://prove2.me/theorems/a2b5be9a-a543-480e-9ff2-79805035afb1
-- title:
--   Posterior-error SPRT — Bayes error and stopped cost
-- statement:
--   Fix a stage $i$. There is a constant $K$ depending only on the stage such that for every target $p\in(0,1]$, the posterior-error SPRT with target $p$ has Bayes error at most $p$ and for both true states $x$,
--   $$\mathbb E_x[c_iT]\le\frac{c_i}{D_{ix}}\Big(\log\frac1p+K\Big).$$
--   This is the upper half of the local logarithmic price.
--
--   Differences from the source:
--   - encoding: $O_i(1)$ → a constant $K$ chosen before $p$; reason: the meaning of the O-term
--   - encoding: Bayes error of a test that stops → a never-stopping tape counts as an error; reason: an event of probability zero; the bound on the expected time rules it out
--   - generalization: rational probabilities, fees and risk parameters → real ones; reason: rationality serves only computability, which is not claimed here; the rational case is an instance
-- source:
--   Zang, Li, Jin, Xu, Causal Failure Rank Determines Statistical Depth, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), App. B.1, proof of Lemma B.1, p.15

import Mathlib
import Definitions.Def_CausalFailureRank_coefficient
import Definitions.Def_CausalFailureRank_tapeLaw
import Definitions.Def_CausalFailureRank_J

open Filter Topology MeasureTheory

namespace CausalFailureRank

variable {N q : ℕ}

open scoped Classical in
/-- **Posterior-error SPRT.** Zang, Li, Jin, Xu, *Causal Failure Rank Determines Statistical Depth*, preprint (STOC 2027 submission, version of 2026-11-03, sha256 721c8b0d…), proof of Lemma B.1, p.15: "A posterior-error SPRT with target p has
Bayes error at most p. … E_x[c_i T] ≤ (c_i/D_ix)(log(1/p) + O_i(1))."

**Formalization Note.** `K` is the `O_i(1)`: it is chosen before `p` and depends only on the stage. A
never-stopping tape counts as an error in the Bayes error. -/
theorem sprt_bound (I : Instance N q) (i : Fin N) :
    ∃ K : ℝ, ∀ p : ℝ, 0 < p → p ≤ 1 →
      stageLaw I i {x | decisionOf (sprtRule I i p) x.2 ≠ some x.1} ≤ ENNReal.ofReal p ∧
      ∀ x : Bool,
        ∫⁻ tape, ENNReal.ofReal (I.c i) * ((stopTime (sprtRule I i p) tape : ℕ∞) : ENNReal)
            ∂(iidLaw I i x) ≤
          ENNReal.ofReal (I.c i / D I i x * (Real.log (1 / p) + K)) := by sorry

end CausalFailureRank
