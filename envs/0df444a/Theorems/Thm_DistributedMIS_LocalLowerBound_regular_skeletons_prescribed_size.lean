-- Prove2me | Theorems.Thm_DistributedMIS_LocalLowerBound_regular_skeletons_prescribed_size
-- name    : DistributedMIS.LocalLowerBound.regular_skeletons_prescribed_size
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:08.607503+00:00
-- url     : https://prove2.me/theorems/b6374995-dae3-4b7d-80ba-718513ace9fe
-- title:
--   Lemma A.5 — Regular skeletons of prescribed size; folklore
-- statement:
--   For integers D,g≥3 define B=1+DΣ_{i=0}^{g-3}(D-1)^i. For every even N>4B there exists a simple D-regular graph H on exactly N vertices with girth at least g. Moreover,
--
--   $$B\le 2D^{g-2}.$$
--
--   The graph size is prescribed, rather than existentially selected along a subsequence. Extended-natural girth gives acyclic graphs girth +∞.
--
--   Differences from the source:
--   - encoding: a graph on N vertices and girth at least g → a SimpleGraph on Fin N and extended-natural egirth≥g; reason: this fixes only a vertex enumeration and preserves the standard infinite girth of acyclic graphs; no regularity or size condition is added
-- source:
--   Seri Khoury, Aaron Schild, STOC 2027 submission #411 (October 2026), pinned submission dated October 30, 2026; Lemma A.5, printed/PDF pp. 34

import Definitions.Def_DistributedMIS_LocalLowerBound_FiniteBlowup

namespace DistributedMIS.LocalLowerBound

theorem regular_skeletons_prescribed_size (D g N : ℕ) (hD : 3 ≤ D) (hg : 3 ≤ g)
    (hN : Even N) (hsize : 4 * regularBallBound D g < N) :
    (∃ H : SimpleGraph (Fin N), (∀ v, by classical exact H.degree v = D) ∧
      (g : ℕ) ≤ H.egirth) ∧ regularBallBound D g ≤ 2 * D^(g-2) := by sorry

end DistributedMIS.LocalLowerBound
