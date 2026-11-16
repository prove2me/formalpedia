-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_Supplement_lemma_5_2
-- name    : FiniteGroupTesting.LinearQuery.Supplement.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:22:17.173568+00:00
-- url     : https://prove2.me/theorems/a0e7dc50-4383-4602-a808-1b371b7ceaa8
-- title:
--   Lemma 5.2 — Fast common locator misses few labels
-- statement:
--   Fix a genuine group of order $n\ge1500$, a positive-length signed generator tuple with spectral accuracy $1/3000$, and a dictionary $D$ with $|D|\ge m/2$, where $1\le m\le n/500$. For $0<\epsilon<1/2$, put $\bar\epsilon=\max(\epsilon,n^{-2})$ and sample one independent common word of length $L=\lceil100(n/m)\log(1/\bar\epsilon)\rceil$. If $Z$ is the fraction of starting labels whose locator misses $D$, then
--   $$\Pr[Z>\bar\epsilon/10000]\le1/100.$$
--   This is a conditional setup guarantee. Starting-label trajectories share the same word, and their miss events are not assumed independent.
--
--   Differences from the source:
--   - generalization: the dictionary and generator tuple produced by the tester, conditioned on the good events → every fixed dictionary and spectral generator tuple satisfying those size bounds; reason: the killed-walk expectation bound is valid conditional on each such setup
--   - encoding: sufficient absolute constants in Sections 4–5 → fixed c_D=1/500, n_0=1500, gamma=1/10000, C_L=100, C_A=2000000, C_P=1000 and globally chosen expansion/fallback parameters; reason: these instantiate the displayed proof estimates uniformly; the predicates selecting numeric constants assume no existence or correctness, and the existing base theorems supply their witnesses
--   - encoding: a genuine input group table ([n],*) whose dictionary walk steps by the queried inverse candidates t_i = s_i^(n-1) → an arbitrary finite group G whose walk steps by s_i and s_i^(-1); reason: on a genuine group t_i = s_i^(-1) by Lagrange (p. 25), and every group table on [n] is such a finite group, so the source instance is covered
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 31, Lemma 5.2

import Definitions.Def_FiniteGroupTesting_LinearQuery_Supplement_UpperTester

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery.Supplement

theorem lemma_5_2 {G : Type} [Group G] [Fintype G] [DecidableEq G]
    (hn : 1500 ≤ Fintype.card G) {k : ℕ} (hk : 0 < k) (s : Fin k → G)
    (hs : CayleyExpansion s spectralAccuracy) (m : ℕ) (hm : 1 ≤ m)
    (hmn : (m : ℝ) ≤ (Fintype.card G : ℝ) / 500) (D : Finset G)
    (hD : (m : ℝ) / 2 ≤ (D.card : ℝ)) (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1/2) :
    uniformProbability (fun σ : Fin (locatorLength (Fintype.card G) m ε) → Signed k =>
      gamma * epsilonBar (Fintype.card G) ε <
        missedFraction (· * ·) (signedMark s) D.toList (List.ofFn σ)) ≤ (1/100 : ℝ) := by sorry

end FiniteGroupTesting.LinearQuery.Supplement
