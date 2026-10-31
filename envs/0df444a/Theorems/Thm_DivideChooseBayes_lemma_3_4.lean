-- Prove2me | Theorems.Thm_DivideChooseBayes_lemma_3_4
-- name    : DivideChooseBayes.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:28:59.976307+00:00
-- url     : https://prove2.me/theorems/97a36da0-681a-4206-8323-275cd8d6bf48
-- title:
--   Lemma 3.4 — Algorithm 1 runs in polynomial time in $n$ and $\sum_i|g^D_i|/\gamma$
-- statement:
--   Let $g^D\in\mathbb R^n$ be divider values, not all zero, let $\mu\in\mathbb R^n$ be prior means and $\sigma\in\mathbb R^n$ standard deviations with $\sigma_i>0$, and let $\gamma>0$. Then:
--
--   1. the main loop of Algorithm 1 runs exactly
--   $$\Big\lceil \frac{\sum_{i=1}^n |g^D_i|}{2\gamma}\Big\rceil$$
--   times;
--   2. for every $0<P\le 1/2$, the program $\mathcal C_P$ in the $n$ variables $q$ has a nonempty, compact, convex feasible set and an affine objective, and attains its maximum.
--
--   So Algorithm 1 solves a number of convex programs that depends only on $\sum_i|g^D_i|/\gamma$, each in $n$ variables with $2n+2$ constraints.
--
--   Differences from the source:
--   - reading: runs in polynomial time in the values of n and Σᵢ|gᴰᵢ|/γ → the loop runs exactly ⌈Σᵢ|gᴰᵢ|/(2γ)⌉ times, and each C_P has a nonempty compact convex feasible set in ℝⁿ, an affine objective and an attained maximum; reason: the algorithm has real inputs, evaluates Φ⁻¹ and asks for exact optima of a second-order-cone program, so no Turing-machine reading exists; this is what the proof of Lemma 3.4 argues (its 'at most 1/(2δ) iterations' is the ceiling ⌈1/(2δ)⌉)
--   - generalization: the programs C_{P_k} at the values P_k the loop uses → C_P for every real 0 < P ≤ 1/2; reason: every P_k on an iteration that runs lies in (0, 1/2]
--   - encoding: Algorithm 1's inputs: divider values not all zero, standard deviations σᵢ > 0, an additive error bound γ → hypotheses gᴰ ≠ 0, σᵢ > 0, γ > 0; reason: the algorithm's own input conditions; γ ≤ 0 or gᴰ = 0 leaves δ ≤ 0 and the while loop does not terminate
-- source:
--   Tucker-Foltz & Zeckhauser, Playing Divide-and-Choose Given Uncertain Preferences, arXiv:2207.03076v2, Lemma 3.4, p.8 (and its proof, pp.8–9)

import Mathlib
import Definitions.Def_DivideChooseBayes_iterationCount
import Definitions.Def_DivideChooseBayes_IsCPOptimal

open MeasureTheory ProbabilityTheory

namespace DivideChooseBayes

/-- **Lemma 3.4 (Algorithm 1 runs in polynomial time).**
Tucker-Foltz & Zeckhauser, *Playing Divide-and-Choose Given Uncertain Preferences*,
arXiv:2207.03076v2, Lemma 3.4, p.8: "Algorithm 1 runs in polynomial time in the values of n and
∑ᵢ|gᴰᵢ| / γ."

For divider values `gᴰ` not all zero, means `m`, standard deviations `σ > 0` and `γ > 0`:
1. the main loop runs exactly `⌈∑ᵢ|gᴰᵢ| / (2γ)⌉` times;
2. for every `0 < P ≤ 1/2` the program `C_P` (n variables) has a nonempty, compact, convex
   feasible set and an affine objective, and attains its maximum.

**Formalization Note.** "Polynomial time" is read as the proof of Lemma 3.4 argues it: a loop
count depending on `∑|gᴰᵢ|/γ` only, and one convex program in `n` variables per iteration. The
algorithm takes real inputs and exact optima of a second-order-cone program, so no Turing-machine
reading applies. The proof's "at most `1/(2δ)` iterations" is the ceiling `⌈1/(2δ)⌉`. -/
theorem lemma_3_4 {ι : Type*} [Fintype ι] (gD m σ : ι → ℝ) (hgD : ∃ i, gD i ≠ 0)
    (hσ : ∀ i, 0 < σ i) (γ : ℝ) (hγ : 0 < γ) :
    iterationCount gD γ = ⌈(∑ i, |gD i|) / (2 * γ)⌉₊ ∧
      ∀ P : ℝ, 0 < P → P ≤ 1 / 2 →
        (cpFeasibleSet gD m σ P).Nonempty ∧ IsCompact (cpFeasibleSet gD m σ P) ∧
          Convex ℝ (cpFeasibleSet gD m σ P) ∧
          (∃ (c₀ : ℝ) (c : ι → ℝ), ∀ q, cpObjective gD P q = c₀ + ∑ i, c i * q i) ∧
          ∃ q, IsCPOptimal gD m σ P q := by sorry

end DivideChooseBayes
