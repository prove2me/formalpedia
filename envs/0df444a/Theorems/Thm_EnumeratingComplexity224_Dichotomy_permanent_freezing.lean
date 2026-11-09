-- Prove2me | Theorems.Thm_EnumeratingComplexity224_Dichotomy_permanent_freezing
-- name    : EnumeratingComplexity224.Dichotomy.permanent_freezing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:33:45.242218+00:00
-- url     : https://prove2.me/theorems/9106b9be-5895-4c70-bc52-695d74a40556
-- title:
--   Lemma 18 — a permanently frozen good tape gives a hard finite subset
-- statement:
--   Fix optimal deterministic and randomized machines, natural parameters $k,l$, and an infinite $S\subseteq\mathbb N$ with $R(S)\ge2^{-k}$. Suppose some good slow tape is in case B: from some moment onward it stays frozen and is never released, including within-stage releases. Then there exists a single finite set $F$ such that
--   $$F\subseteq S,\qquad D(F)>l,\qquad R_N(F\mid k,l)\ge2^{-k-2}.$$
--   The probability is for exact limiting output of the specific constructed slow process, rather than the probability of ever visiting $F$. Both inequalities concern this same finite $F$. All infinite-tape and stage limits are retained, and the threshold is exactly one quarter of $2^{-k}$. This is the whole conclusion of Lemma 18.
--
--   Differences from the source:
--   - encoding: Turing machines with finite padded binary inputs and non-halting output → finite partial-recursive instruction codes with padded cell reads, a sequential fair-bit interface and append-only natural-number messages; D takes values in the extended naturals and probabilities are extended nonnegative reals; reason: the interpreter gives effective finite simulations and the same infinite enumerations; program length is still the exact binary input length
--   - generalization: fixed optimal machines and the p.6 convention D(S)>0 and R(S)≤1/4 when using logarithmic bounds → arbitrary fixed optimal machines, without the logarithmic normalization; reason: the p.6 convention sets aside finitely many exceptional sets to make logarithms defined; the selected logarithm-free source arguments apply to all optimal machine choices and all their sets
--   - encoding: any eligible collecting choice in the stage process of §3.1 → least finite-set binary code among all subsets of the finite fast-output union, with 2^(k+2) collecting attempts and identity attempts after exhaustion; reason: this is a computable permitted tie-break; the source proves at most 2^(k+2) successful iterations
--   - reading: cases A, B and C refer to moments throughout the scattering/collecting process → release and collecting event flags are retained within each stage; case B forbids every later release, even when refreezing occurs in that stage; reason: p.9 explicitly allows two transitions in one stage and the proof of Lemma 18 requires continuous freezing, not just frozen stage endpoints
-- source:
--   Alexander Shekhovtsov, Nikolay Vereshchagin, Georgii Zakharov, Enumerating Complexity Revisited, STOC 2027 submission #224 (October 2026), p. 10, Lemma 18 with §3 preamble, p.7

import Definitions.Def_EnumeratingComplexity224_Dichotomy_Process

namespace EnumeratingComplexity224.Dichotomy

/-- Whole Lemma 18, p.10: the SAME finite F satisfies both inequalities. -/
theorem permanent_freezing (m p : Machine)
    (hm : OptimalDeterministic m) (hp : OptimalRandom p)
    (k l : ℕ) (S : Set ℕ) (hS : S.Infinite)
    (hR : ENNReal.ofReal (dyadic k) ≤ probability p S [])
    (hB : ∃ w : Tape, enumerated p [] [] w = S ∧ caseB m p k l w) :
    ∃ F : Finset ℕ, (↑F : Set ℕ) ⊆ S ∧ (l : ℕ∞) < complexity m (↑F : Set ℕ) ∧
      ENNReal.ofReal (dyadic (k + 2)) ≤ slowProbability m p k l (↑F : Set ℕ) := by sorry

end EnumeratingComplexity224.Dichotomy
