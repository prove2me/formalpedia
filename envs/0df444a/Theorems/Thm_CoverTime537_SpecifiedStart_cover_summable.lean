-- Prove2me | Theorems.Thm_CoverTime537_SpecifiedStart_cover_summable
-- name    : CoverTime537.SpecifiedStart.cover_summable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:22.712886+00:00
-- url     : https://prove2.me/theorems/ba6008ba-960b-4732-8c71-4987cc545dae
-- title:
--   Convergence of ordinary cover and last-discovery series
-- statement:
--   For every finite connected simple graph $H$ and starting vertex $x$, the uncovered-at-time-$t$ probabilities are summable, as are the probabilities of first discovering any prescribed last vertex at time $t$:
--
--   $$\sum_{t\ge0}\mathbb P_x(\tau_H>t)<\infty.$$
--
--   The singleton is included and its cover series is identically zero. This is a supporting convergence target for the expectation convention; it supplies no additional hypothesis to another theorem.
--
--   Differences from the source:
--   - encoding: walk expectation and event probabilities → finite trajectory cylinder probabilities and real tail sums; reason: time zero and all ordinary walk instances are preserved; convergence is a separate supporting target, never an added premise
-- source:
--   Ryan Aghazadeh, STOC 2027 submission #537 (October 2026), §1 p.2 expectation (1), §3 p.7 finiteness of expectations

import Definitions.Def_CoverTime537_SpecifiedStart_Walk

namespace CoverTime537.SpecifiedStart
/-- Supporting convergence obligation for the p.2 expectation and p.7 finite
expectation convention. It is a target, never an extra hypothesis of Lemma 5
or Theorem 1. Connectivity includes the singleton; no aperiodicity is needed. -/
theorem cover_summable {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (hc : H.Connected) (x : V) :
    Summable (MarkovMixing.coverTailProb (walk H) x) ∧
    (∀ v, Summable (lastAt H x v)) := by sorry
end CoverTime537.SpecifiedStart
