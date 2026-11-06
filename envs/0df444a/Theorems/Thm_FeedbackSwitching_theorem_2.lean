-- Prove2me | Theorems.Thm_FeedbackSwitching_theorem_2
-- name    : FeedbackSwitching.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:43:30.834211+00:00
-- url     : https://prove2.me/theorems/d6f77d34-6152-4bee-a014-d2230229f015
-- title:
--   Theorem 2 — TournamentSteering: $\mathrm{Reg}_T\le2^{40}\min\{T,\sqrt{T\log K}\log^2(eKT)\}$ on strongly revealing graphs
-- statement:
--   For every $K,T\ge1$, every known, fixed strongly revealing graph $G$, every tournament orientation of $G$ whose edges $s\to j$ have sources observing both losses, and every choice of optimal LP solutions, TournamentSteering (Algorithm 1 with the parameters of §4.6) satisfies, against every oblivious loss sequence $\ell\in[0,1]^{T\times K}$,
--   $$
--   \mathrm{Reg}_T\le2^{40}\min\Big\{T,\ \sqrt{T\log K}\,\log^2(eKT)\Big\}.
--   $$
--   This is the upper bound of the $\sqrt T$ regime; it depends on $K$ only through $\log K$ and logarithmic factors.
--
--   **Formalization Note** The algorithm plays against $G$ and reads only the revealed losses. The first clause asserts that the cost in Eq. (12) is integrable over the coins. $\log$ is natural.
--
--   Differences from the source:
--   - reading: TournamentSteering with "a selected orientation" (Proposition 1) and "a solution of the LP" (Algorithm 3) → every orientation A of G whose edges have sources observing both losses, and every selection sel of optimal LP solutions; reason: the paper fixes these choices without specifying them; the statement holds for each, so it is stated for all
--   - encoding: K ≥ 1; "play a fixed action" → NeZero K; action 0; reason: Fin K is nonempty exactly when K ≥ 1; the fixed action is unspecified in the paper and every fixed action has the same regret bound
--   - encoding: the expectation in Eq. (12) → the Bochner integral over the coins, with a clause asserting that the integrand is integrable; reason: the paper's expectation exists; the clause rules out Lean's junk value 0 of a non-integrable integral and changes no instance
--   - encoding: actions [K], rounds 1..T, the learner observes ℓ_t(j) for every (I_t, j) ∈ E → actions Fin K, rounds 0..T−1, the learner receives the vector reveal G ℓ_t I_t (observed coordinates, others masked to 0); reason: the mask is determined by I_t and G, both known to the learner, so the vector carries exactly the observed losses; same instances
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Theorem 2, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_FeedbackSwitching_StronglyRevealing
import Definitions.Def_FeedbackSwitching_regret
import Definitions.Def_FeedbackSwitching_tournamentSteering
open MeasureTheory

namespace FeedbackSwitching

/-- **Theorem 2 (Strongly revealing graphs)**, p.23 (PDF p.25). Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, *The Price of Partial Information with
Switching Costs: A Complete Characterization for Feedback Graphs*, arXiv:2606.03851 (held version,
sha256 ded8f8bc…).

"For every `K, T ≥ 1` and every known, fixed strongly revealing graph, TournamentSteering
(Algorithm 1) satisfies, against every oblivious loss sequence,
`Reg_T ≤ 2^{40} min{T, √(T log K) log²(eKT)}`."

**Formalization Note.** TournamentSteering is `tournamentSteering A sel T`: Algorithm 1 with the
§4.6 parameters, for any orientation `A` of `G` whose edges `s → j` have sources observing both
losses (Proposition 1) and any selection `sel` of optimal LP solutions (Algorithm 3: "a solution of
the LP"). It plays against `G` and reads only the revealed losses. `K ≥ 1` is `NeZero K`. The
first clause asserts that the expected cost in Eq. (12) is the integral of an integrable function. -/
theorem theorem_2 {K T : ℕ} [NeZero K] (hT : 1 ≤ T) (G : FeedbackGraph K)
    (hG : StronglyRevealing G) (A : Fin K → Fin K → Prop) (hA : IsObservedOrientation G A)
    (sel : (Fin K → ℝ) → (Fin K → Matrix (Fin K) (Fin K) ℝ) × (Fin K → ℝ))
    (hsel : ∀ w, IsPosProbVec w → IsOptimalAssignment A w (sel w)) (ℓ : LossSeq K T) :
    Integrable (fun ω => pathLoss ℓ.1 (action G (tournamentSteering A sel T) ℓ.1 ω)
      + pathSwitches T (action G (tournamentSteering A sel T) ℓ.1 ω))
      (tournamentSteering A sel T).μ ∧
    regret G (tournamentSteering A sel T) ℓ.1 ≤
      2 ^ 40 * min (T : ℝ)
        (Real.sqrt (T * Real.log K) * Real.log (Real.exp 1 * K * T) ^ 2) := by sorry

end FeedbackSwitching
