-- Prove2me | Theorems.Thm_FeedbackSwitching_theorem_3
-- name    : FeedbackSwitching.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:45:34.197192+00:00
-- url     : https://prove2.me/theorems/ed658431-729f-4606-ad09-a15fe8f9c140
-- title:
--   Theorem 3 — LazyExploration on observable graphs: $\mathrm{Reg}_T\le3^{4/3}(|D|\log K)^{1/3}T^{2/3}$
-- statement:
--   Let $G$ be an observable graph on $K\ge2$ actions with an observing set $D$, and let $T\ge1$. Put
--   $$
--   \kappa=\Big(\frac{|D|\log K}{9T}\Big)^{1/3},\qquad\eta=\sqrt{\frac{\kappa\log K}{T|D|}} .
--   $$
--   1. If $\kappa\le\frac12$, LazyExploration (Algorithm 4) with $D,\kappa,\eta$ satisfies, against every oblivious loss sequence,
--   $$
--   \mathrm{Reg}_T\le3^{4/3}(|D|\log K)^{1/3}T^{2/3}.
--   $$
--   2. If $\kappa>\frac12$, every fixed action has regret at most $(|D|\log K)^{1/3}T^{2/3}$ against every loss sequence.
--
--   With $|D|=\gamma(G)$ this is the upper bound of the $T^{2/3}$ regime.
--
--   **Formalization Note** Algorithm 4 runs on i.i.d. uniform coins and reads only the revealed losses; the first clause also asserts that its cost is integrable. Powers are real powers.
--
--   Differences from the source:
--   - encoding: the expectation in Eq. (12) → the Bochner integral over the coins, with a clause asserting that the integrand is integrable; reason: the paper's expectation exists; the clause rules out Lean's junk value 0 of a non-integrable integral and changes no instance
--   - encoding: actions [K], rounds 1..T, the learner observes ℓ_t(j) for every (I_t, j) ∈ E → actions Fin K, rounds 0..T−1, the learner receives the vector reveal G ℓ_t I_t (observed coordinates, others masked to 0); reason: the mask is determined by I_t and G, both known to the learner, so the vector carries exactly the observed losses; same instances
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Theorem 3, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_FeedbackSwitching_regret
import Definitions.Def_FeedbackSwitching_lazyExploration
open MeasureTheory

namespace FeedbackSwitching

/-- **Theorem 3 (Observable graphs)**, p.34 (PDF p.36). Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, *The Price of Partial Information with
Switching Costs: A Complete Characterization for Feedback Graphs*, arXiv:2606.03851 (held version,
sha256 ded8f8bc…).

"Let `G` be an observable graph on `K ≥ 2` actions with an observing set `D`, and let `T ≥ 1`. With
`κ = (|D| log K/(9T))^{1/3}` and `η = √(κ log K/(T|D|))`, if `κ ≤ 1/2`, Algorithm 4 satisfies
`Reg_T ≤ 3^{4/3} (|D| log K)^{1/3} T^{2/3}`. If `κ > 1/2`, a fixed action has regret at most
`(|D| log K)^{1/3} T^{2/3}`."

**Formalization Note.** Algorithm 4 is `lazyExploration G D κ η` on i.i.d. uniform coins; it
reads only the revealed losses. `κ = lzKappa K T |D|`, `η = lzEta K T |D|`. Both bounds hold against every loss sequence; the second for every
fixed action `i` (`constPolicy i`). Real powers are `Real.rpow`. The first clause also asserts
that the expected cost in Eq. (12) is the integral of an integrable function. -/
theorem theorem_3 {K T : ℕ} [NeZero K] (hK : 2 ≤ K) (hT : 1 ≤ T) (G : FeedbackGraph K)
    (hG : Observable G) (D : Finset (Fin K)) (hD : IsObservingSet G D) :
    (lzKappa K T D.card ≤ 1 / 2 →
      ∀ ℓ : LossSeq K T,
        Integrable (fun ω =>
            pathLoss ℓ.1
              (action G (lazyExploration G D (lzKappa K T D.card) (lzEta K T D.card)) ℓ.1 ω)
            + pathSwitches T
              (action G (lazyExploration G D (lzKappa K T D.card) (lzEta K T D.card)) ℓ.1 ω))
          (lazyExploration G D (lzKappa K T D.card) (lzEta K T D.card)).μ ∧
        regret G (lazyExploration G D (lzKappa K T D.card) (lzEta K T D.card)) ℓ.1
          ≤ (3 : ℝ) ^ ((4 : ℝ) / 3) * ((D.card : ℝ) * Real.log K) ^ ((1 : ℝ) / 3) *
              (T : ℝ) ^ ((2 : ℝ) / 3)) ∧
    (1 / 2 < lzKappa K T D.card →
      ∀ (i : Fin K) (ℓ : LossSeq K T),
        regret G (constPolicy i) ℓ.1
          ≤ ((D.card : ℝ) * Real.log K) ^ ((1 : ℝ) / 3) * (T : ℝ) ^ ((2 : ℝ) / 3)) := by sorry

end FeedbackSwitching
