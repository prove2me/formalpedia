-- Prove2me | Theorems.Thm_FeedbackSwitching_proposition_4
-- name    : FeedbackSwitching.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:41:18.810622+00:00
-- url     : https://prove2.me/theorems/c388ada3-3b0d-4082-a221-2802800afd77
-- title:
--   Proposition 4 — every learner suffers $\frac{T^{2/3}}{256\log_2(2T)}(\min\{|S|,T\}/m)^{1/3}$ on some loss sequence
-- statement:
--   Let $G$ be a directed graph on $K\ge2$ actions, and let $S$ be a set of at least two actions in which every member observes at most one member of $S$. Let $m\ge1$ (a real number) be such that every action observes at most $m$ members of $S$, and let $T\ge2$. For every learner there is an oblivious loss sequence on which
--   $$
--   \mathrm{Reg}_T\ge\frac{T^{2/3}}{256\log_2(2T)}\Big(\frac{\min\{|S|,T\}}{m}\Big)^{1/3}.
--   $$
--   A single pair without an observing endpoint ($m=2$) already forces rate $T^{2/3}$, and a large set observed only a few at a time forces a rate growing with its size.
--
--   **Formalization Note** "Observes" counts self-loops. $\log_2$ is the base-2 logarithm.
--
--   Differences from the source:
--   - reading: the infimum over learners ("the learner selects I_t based on its past observations and randomization"; no measurability stated) → the infimum over Learner K: randomized policies on a probability space of coins that see only the revealed losses and are jointly measurable in (history, coins); reason: the lower-bound proofs (Proposition 4, Appendix G) average over random loss sequences and take the law of the transcript, which needs joint measurability; the algorithms giving the upper bounds are measurable
--   - encoding: actions [K], rounds 1..T, the learner observes ℓ_t(j) for every (I_t, j) ∈ E → actions Fin K, rounds 0..T−1, the learner receives the vector reveal G ℓ_t I_t (observed coordinates, others masked to 0); reason: the mask is determined by I_t and G, both known to the learner, so the vector carries exactly the observed losses; same instances
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Proposition 4, p.36 (PDF p.38)

import Mathlib
import Definitions.Def_FeedbackSwitching_regret
open MeasureTheory
open scoped Classical

namespace FeedbackSwitching

/-- **Proposition 4**, p.36 (PDF p.38). Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, *The Price of Partial Information with
Switching Costs: A Complete Characterization for Feedback Graphs*, arXiv:2606.03851 (held version,
sha256 ded8f8bc…).

"Let `G` be a directed graph on `K ≥ 2` actions, and let `S` be a set of at least two actions in
which every member observes at most one member of `S`. Let `m ≥ 1` be such that every action
observes at most `m` members of `S`, and let `T ≥ 2`. For every learner there is an oblivious loss
sequence on which `Reg_T ≥ T^{2/3}/(256 log₂(2T)) · (min{|S|, T}/m)^{1/3}`."

**Formalization Note.** `m` is real (Theorem 4 applies it with `m = log(eK)`). "Every learner"
ranges over `Learner K`: randomized learners that see only the revealed losses and are jointly
measurable in (history, coins). "Observes" counts self-loops: `u` observes `v` iff `G u v`.
`log₂` is `Real.logb 2`; powers are `Real.rpow`. -/
theorem proposition_4 {K T : ℕ} (hK : 2 ≤ K) (G : FeedbackGraph K) (S : Finset (Fin K))
    (hS : 2 ≤ S.card) (hSS : ∀ u ∈ S, (S.filter (fun v => G u v)).card ≤ 1)
    (m : ℝ) (hm : 1 ≤ m) (hobs : ∀ a, ((S.filter (fun v => G a v)).card : ℝ) ≤ m)
    (hT : 2 ≤ T) :
    ∀ L : Learner K, ∃ ℓ : LossSeq K T,
      (T : ℝ) ^ ((2 : ℝ) / 3) / (256 * Real.logb 2 (2 * T)) *
          (min (S.card : ℝ) T / m) ^ ((1 : ℝ) / 3)
        ≤ regret G L.toPolicy ℓ.1 := by sorry

end FeedbackSwitching
