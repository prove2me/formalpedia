-- Prove2me | Theorems.Thm_FeedbackSwitching_proposition_1
-- name    : FeedbackSwitching.proposition_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T00:40:28.311194+00:00
-- url     : https://prove2.me/theorems/e181b126-e4c2-4eb9-a73f-459a32426e84
-- title:
--   Proposition 1 — strongly revealing ⇔ contains a spanning strongly observable tournament; a pairwise rule selects an observed orientation
-- statement:
--   For every feedback graph $G$:
--
--   1. $G$ is strongly revealing (Eq. (13)) if and only if it contains a spanning strongly observable tournament.
--   2. There is one rule, applied to the four graph entries $(i,i),(i,j),(j,i),(j,j)$ of each pair $i<j$, that for every strongly revealing graph selects a tournament orientation in which playing $s$ reveals $\Delta_t(s,j)=\ell_t(s)-\ell_t(j)$ for every edge $s\to j$, i.e. $(s,s)\in E$ and $(s,j)\in E$. This orientation is selected in $O(K^2)$ graph operations.
--
--   The proposition reduces strongly revealing graphs to tournaments whose comparisons are observable, which is all the algorithm of §4 uses.
--
--   Differences from the source:
--   - encoding: one can select a tournament orientation in O(K²) graph operations → there is one rule on the four graph entries of each pair, fixed before K and G, whose orientation is observed for every strongly revealing graph; reason: the proof selects each direction by inspecting a constant number of entries per pair; a pairwise rule of four entries costs O(1) per pair, O(K²) in all, and Lean has no cost model to state the operation count directly
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Proposition 1, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_FeedbackSwitching_StronglyRevealing
import Definitions.Def_FeedbackSwitching_IsTournament

namespace FeedbackSwitching

/-- **Proposition 1 (Reduction to observable comparisons)**, p.14 (PDF p.16). Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, *The Price of Partial Information with
Switching Costs: A Complete Characterization for Feedback Graphs*, arXiv:2606.03851 (held version,
sha256 ded8f8bc…).

"The pairwise condition in Eq. (13) is equivalent to containing a spanning strongly observable
tournament. When it holds, one can select a tournament orientation in `O(K²)` graph operations
such that playing `s` reveals `Δ_t(s, j)` for every edge `s → j`."

**Formalization Note.** A spanning strongly observable tournament is a pair `(A, L)` (tournament
and retained self-loops) as defined on p.14 (`IsSpanningSOTournament`). "In `O(K²)` graph
operations" is encoded as locality: one rule, fixed before `K` and `G`, applied to the four
graph entries `(G i i, G i j, G j i, G j j)` of each pair `i < j` (`orientByRule`), yields for
every strongly revealing graph an orientation whose every edge `s → j` has a source observing
both losses (`IsObservedOrientation`). -/
theorem proposition_1 :
    (∀ (K : ℕ) (G : FeedbackGraph K),
      StronglyRevealing G ↔ ∃ (A : Fin K → Fin K → Prop) (L : Fin K → Prop),
        IsSpanningSOTournament G A L) ∧
    ∃ rule : Prop → Prop → Prop → Prop → Prop,
      ∀ (K : ℕ) (G : FeedbackGraph K), StronglyRevealing G →
        IsObservedOrientation G (orientByRule rule G) := by sorry

end FeedbackSwitching
