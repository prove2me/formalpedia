-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_Supplement_lemma_4_1
-- name    : FiniteGroupTesting.LinearQuery.Supplement.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:19:48.77044+00:00
-- url     : https://prove2.me/theorems/9a2cfbbc-ab14-441d-93e3-bf1f833b505f
-- title:
--   Lemma 4.1 — Dictionary size on a spectral group walk
-- statement:
--   Let $G$ be a group of order $n\ge1500$, and fix $k>0$ signed generators whose symmetric Cayley operator has spectral accuracy $1/3000$. For $1\le m\le n/500$, start at a uniform group element and take $m$ independent uniform signed steps. If $D$ is the set of visited labels, including the start, then
--   $$\Pr[|D|\ge m/2]\ge99/100.$$
--   This is the dictionary-size guarantee conditioned on a fixed good spectral setup. It is uniform in the group, the spectral tuple and the allowed dictionary length.
--
--   Differences from the source:
--   - generalization: the randomly selected generator tuple, conditioned on its spectral event → every fixed positive-length generator tuple satisfying that spectral bound; reason: the collision estimate is pointwise in the fixed Cayley operator and therefore specializes to the stated conditional law
--   - encoding: an absolute n_0 and fixed c_D<=1/500, lambda_0<=1/3000 → n_0=1500, c_D=1/500 and lambda_0=1/3000; reason: the proof on pp. 25–26 gives E[C_coll]/m<=3/1000 at these values
--   - encoding: a genuine input group table ([n],*) whose dictionary walk steps by the queried inverse candidates t_i = s_i^(n-1) → an arbitrary finite group G whose walk steps by s_i and s_i^(-1); reason: on a genuine group t_i = s_i^(-1) by Lagrange (p. 25), and every group table on [n] is such a finite group, so the source instance is covered
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 25, Lemma 4.1

import Definitions.Def_FiniteGroupTesting_LinearQuery_Supplement_UpperTester

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery.Supplement

theorem lemma_4_1 {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (hn : 1500 ≤ Fintype.card G) {k : ℕ} (hk : 0 < k) (s : Fin k → G)
    (hs : CayleyExpansion s spectralAccuracy) (m : ℕ) (hm : 1 ≤ m)
    (hmn : (m : ℝ) ≤ (Fintype.card G : ℝ) / 500) :
    (99/100 : ℝ) ≤ uniformProbability (fun sample : G × (Fin m → Signed k) =>
      (m : ℝ) / 2 ≤ ((walk (· * ·) (signedMark s) sample.1
        (List.ofFn sample.2)).toFinset.card : ℝ)) := by sorry

end FiniteGroupTesting.LinearQuery.Supplement
