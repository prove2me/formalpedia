-- Prove2me | Theorems.Thm_BetterKMedian_LMPGreedy_theorem_1_3
-- name    : BetterKMedian.LMPGreedy.theorem_1_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:21:06.562243+00:00
-- url     : https://prove2.me/theorems/ca3f65ad-c23a-4fb0-82b4-c14cd582bfda
-- title:
--   Theorem 1.3 — a polynomial-time $1.9499$-LMP approximation algorithm for uncapacitated facility location
-- statement:
--   There is one deterministic polynomial-time algorithm — a Mathlib `Turing.TM2ComputableInPolyTime` machine with finite tape alphabets — that reads the binary code of any uncapacitated facility location instance with rational data (pseudometric distances, uniform opening cost $f\ge0$) and outputs the indicator bit-list of a set $S\subseteq F$ that is a solution (nonempty when there are clients) with
--   $$\sum_{j\in D}d(j,S)\le1.9499\,\bigl(\mathrm{OPT}_f-f\,|S|\bigr).$$
--
--   Differences from the source:
--   - encoding: "a polynomial-time algorithm" (no machine model named) → one `Turing.TM2ComputableInPolyTime RatInstance.encode id alg` witness with every tape alphabet finite, input the binary code `RatInstance.encode`, output the `List Bool` indicator of S; reason: the paper names no model; a multi-tape Turing machine polynomial in the input bit length is the standard meaning, and the same model as the published `OAI.MetricKMedian.main_finite_work`
--   - encoding: UFL instances with real data → instances with rational distances and opening cost (`RatInstance`), read as real instances by `toReal`; reason: an algorithm on a Turing machine receives finite input; rational data is the standard input model
--   - reading: a metric d(·,·) on D ∪ F (§2, p. 5) → a real pseudometric `d` on points `Fin N` (nonnegative, symmetric, zero diagonal, triangle inequality; distinct points may be at distance 0), clients and facilities `Finset (Fin N)` that may overlap; reason: the paper's own examples (Figures 1–3, pp. 8–10) place clients at distance 0 from facilities, so "metric" is read as pseudometric; a metric is a special case
--   - generalization: §2 standing assumption (3): 1 ≤ d(i,j) ≤ poly(|D|) for i ∈ F, j ∈ D (p. 5) → no such assumption: every instance; reason: (3) is introduced as a k-median reduction "as in [CGL+25, Lemma 2.1]", while the facility-location results are claimed for every UFL instance; the Lean statement covers all instances and specializes to those satisfying (3) (see INSIGHTS I1)
--   - encoding: an instance of UFL → `Instance` requires a facility whenever there is a client (`facilities_nonempty`); reason: with D ≠ ∅ and F = ∅ every solution has cost +∞ and OPT_f is undefined; the condition only excludes undefined cases
--   - encoding: d(j, S) = min_{i∈S} d(i, j) with d(j, ∅) = +∞ (§2) → `distToSet S j` is the minimum for nonempty S and 0 for S = ∅; a solution must be nonempty when D ≠ ∅ (`IsFeasible`); reason: an empty S has infinite cost exactly when D ≠ ∅; feasibility encodes that, and the value at ∅ is never used by a feasible solution with clients
--   - encoding: OPT_f, the optimum value (§2) → `I.OPT`: the minimum of cost_f over the finite nonempty family of solutions; reason: same value
--   - encoding: the constant 1.9499 → the real `19499 / 10000`; reason: exact value
-- source:
--   Buhai, Cohen-Addad, Fleischmann, Gupta, Jubés Monforte, Pittu, Stouras, Svensson, Vogl, A Better-than-2 Approximation for k-Median (2026), STOC 2027 submission, SHA-256 5c2605b2…f461, Theorem 1.3, printed p. 3 (PDF 5); Definition 2.1, printed p. 6 (PDF 8)

import Mathlib
import Definitions.Def_BetterKMedian_LMPGreedy_Encoding

set_option autoImplicit false

namespace BetterKMedian.LMPGreedy

/-- **Theorem 1.3** (Buhai et al. 2026, printed p. 3, PDF 5). There exists a polynomial-time
`1.9499`-LMP approximation algorithm for uncapacitated facility location: one Turing machine
(Mathlib `TM2ComputableInPolyTime`, every tape alphabet finite) that reads the binary code of any
UFL instance with rational data and uniform opening cost `f ≥ 0`, and outputs the indicator
bit-list of a solution `S ⊆ F` with `Σ_{j ∈ D} d(j, S) ≤ 1.9499 · (OPT_f − f · |S|)`. -/
theorem theorem_1_3 :
    ∃ (alg : RatInstance → List Bool)
      (P : Turing.TM2ComputableInPolyTime RatInstance.encode id alg),
      (∀ k : P.tm.K, Finite (P.tm.Γ k)) ∧
      ∀ I : RatInstance, RatInstance.LMPCorrect (19499 / 10000) I (alg I) := by sorry

end BetterKMedian.LMPGreedy
