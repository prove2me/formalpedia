-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_eq_26
-- name    : EdgeSublinearMWIS.Main.eq_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T13:45:32.886789+00:00
-- url     : https://prove2.me/theorems/6e0a212c-7159-4c32-b6df-a340c4cc7375
-- title:
--   Section 5.3, Eq. (26) — runtime of Algorithms 1–2
-- statement:
--   Fix a promised class, integer $a\ge2$ and its uniform bound (2). One finite program implements the same operational Solve, including every ellipsoid query and recursive child. For $n\ge2$ and rational $0<\varepsilon<1$, it first rounds to $\varepsilon/2<\varepsilon'\le\varepsilon$, fixes $\lambda,\delta,p,r$ from $n,\varepsilon'$, and returns the actual pair $(I_G,u_G)$. Its charged time obeys all four source upper-bound forms,
--   $$n^{O(r\lambda)}=2^{O(r\lambda^2)}=2^{O_{\mathcal C}(p\lambda^3)}=2^{O_{\mathcal C}(\varepsilon^{-(4a-2)}(\log_2n)^{8a-1})},$$
--   plus additive polynomial time in the original accuracy encoding length. One positive comparison constant is chosen before every graph and accuracy; the preprocessing exponent is universal. Correctness of the primitive implementations, the recursion invariant and implementation by genuine finite-program runs are conclusions. No free feasibility calls, assigned clocks or uncharged rational operations occur in the statement. The goal handles $n\le1$ directly.
--
--   Differences from the source:
--   - encoding: arbitrary finite simple graphs → graphs labeled by Fin n and finite vertex masks; reason: every finite graph admits such a labeling; induced injections transport class membership
--   - encoding: Algorithms 1–2 with correct separator and exact rational feasibility implementations → raw finite subprograms and their correctness as existential conclusions, plus the explicit Execute relation; reason: the operational definition supplies all control flow; termination and invariant are proved properties, not constructor assumptions
--   - encoding: an unspecified class-uniform threshold p=O_C((delta inverse log n)^(4a-2)), nondecreasing in n → max(1,ceil(B (h(n)/delta)^(4a-2))) for one positive integer B before all inputs; reason: p may be enlarged by the p.11 monotonicity argument; h(n) is within universal constant factors of log_2 n
--   - encoding: runtime after dyadic rounding → each of the four upper bounds plus additive polynomial work on the original accuracy encoding; reason: §5.3 explicitly permits polynomial preprocessing of arbitrary rational accuracy encodings
--   - encoding: O and O_C notation → one positive class-uniform constant before all inputs and a universal preprocessing exponent; reason: all exact source exponents are retained; no numerical ellipsoid constant is invented
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), Section 5.3, Eq. (26), p.19 (PDF p.19), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_AlgorithmContracts

namespace EdgeSublinearMWIS.Main

/-- Section 5.3 Eq. (26). The same operational Solve is implemented by one finite
program, with all subcalls charged, after polynomial dyadic preprocessing. -/
theorem eq_26 :
    ∃ q : ℕ, 0 < q ∧ ∀ (C : GraphClass) (a : ℕ) (K : ℝ),
      StronglyEdgeSublinear C → 2 ≤ a → TreewidthBound C a K →
      ∃ (B : ℕ) (M : Routines) (U : Program) (D : ℝ),
        0 < B ∧ 0 < D ∧ PrimitiveContract C a B M ∧ SolveInvariant C a B M ∧
        ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (ε : RationalCode),
          2 ≤ n → C n G → 0 < ε.value → ε.value < 1 →
          let e := roundedAccuracy ε.value
          let P := parameters B a n e
          ε.value / 2 < e ∧ e ≤ ε.value ∧
          ∃ (I : Finset (Fin n)) (u t : ℕ),
            Execute G P M (.solve Finset.univ) (.solved I u) ∧
            Runs U (unweightedInput G ε) (mask I ++ encodeNat u) t ∧
            (t : ℝ) ≤ D * (ε.bits.length + 1 : ℝ) ^ q +
              D * (n : ℝ) ^ (D * (P.r * P.lambda : ℕ)) ∧
            (t : ℝ) ≤ D * (ε.bits.length + 1 : ℝ) ^ q +
              D * (2 : ℝ) ^ (D * (P.r * P.lambda ^ 2 : ℕ)) ∧
            (t : ℝ) ≤ D * (ε.bits.length + 1 : ℝ) ^ q +
              D * (2 : ℝ) ^ (D * (P.p * P.lambda ^ 3 : ℕ)) ∧
            (t : ℝ) ≤ D * (ε.bits.length + 1 : ℝ) ^ q +
              D * (2 : ℝ) ^ (D * (ε.value : ℝ)⁻¹ ^ (4 * a - 2) *
                logTwo n ^ (8 * a - 1)) := by sorry

end EdgeSublinearMWIS.Main
