-- Prove2me | Theorems.Thm_EnumeratingComplexity224_Dichotomy_process_properties
-- name    : EnumeratingComplexity224.Dichotomy.process_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:34:15.775397+00:00
-- url     : https://prove2.me/theorems/280da6c9-0c47-490f-9158-69dd244ecc2a
-- title:
--   Lemma 14 — monotonicity, finite-prefix dependence and effectiveness
-- statement:
--   Fix the deterministic and randomized codes $M,P$. For every $k,l,t\in\mathbb N$ and tape $w$, the constructed slow process satisfies
--   $$N^t(w)\subseteq P^t(w),\qquad N^t(w)\subseteq N^{t+1}(w),\qquad N(w)\subseteq P(w).$$
--   For each $t$, both fast output and the complete slow row, including its state, depend only on the first $t$ bits. At every intermediate collecting iteration of a positive stage, for every finite $F$, the probability in equation (3) is precisely the eligible-row count divided by $2^t$. Stage tables are computable from $k,l,t$ for the fixed codes. The collecting loop ends with no eligible batch of the required mass.
--
--   There is one conditional machine code $N$ realizing the limiting slow output simultaneously for every auxiliary pair and every tape:
--   $$\forall k,l,w,\quad N(w,\langle k\rangle l)=\bigcup_tN^t(w).$$
--   Its exact-output events are measurable for every set. This includes both parts (a) and (b): legitimacy as an effective enumerator, monotonicity, containment, finite-prefix dependence, rational probabilities and uniform process computability. It does not take these properties as hypotheses on an unspecified process.
--
--   Differences from the source:
--   - encoding: Turing machines with finite padded binary inputs and non-halting output → finite partial-recursive instruction codes with padded cell reads, a sequential fair-bit interface and append-only natural-number messages; D takes values in the extended naturals and probabilities are extended nonnegative reals; reason: the interpreter gives effective finite simulations and the same infinite enumerations; program length is still the exact binary input length
--   - encoding: any eligible collecting choice in the stage process of §3.1 → least finite-set binary code among all subsets of the finite fast-output union, with 2^(k+2) collecting attempts and identity attempts after exhaustion; reason: this is a computable permitted tie-break; the source proves at most 2^(k+2) successful iterations
--   - reading: cases A, B and C refer to moments throughout the scattering/collecting process → release and collecting event flags are retained within each stage; case B forbids every later release, even when refreezing occurs in that stage; reason: p.9 explicitly allows two transitions in one stage and the proof of Lemma 18 requires continuous freezing, not just frozen stage endpoints
--   - encoding: the auxiliary string ⟨k⟩l with binary naturals and a self-delimiting first component → little-endian binary with zero [false], unary binary-length prefix for k, and a padded end marker after l; reason: this is a computable prefix-decodable convention with first-component length 2 log₂ k+O(1); it changes no pair instance
--   - generalization: Lemma 14 is stated for the two fixed optimal machines → the full process properties hold for every pair of concrete machine codes; reason: none of the operational properties uses optimality, and the fixed optimal pair is included
-- source:
--   Alexander Shekhovtsov, Nikolay Vereshchagin, Georgii Zakharov, Enumerating Complexity Revisited, STOC 2027 submission #224 (October 2026), p. 8, Lemma 14(a,b), equation (3), and Remark 15

import Definitions.Def_EnumeratingComplexity224_Dichotomy_Process

namespace EnumeratingComplexity224.Dichotomy

/-- Whole Lemma 14(a,b), p.8. A single conditional code realizes every (k,l).
Stage-table computability is asserted on natural encodings, not assumed. -/
theorem process_properties (m p : Machine) :
    (∀ (k l t : ℕ) (w : Tape),
      position (slowState m p k l t w) ⊆ stageOutput p [] [] w t) ∧
    (∀ (k l : ℕ) (w : Tape), Monotone (fun t => position (slowState m p k l t w))) ∧
    (∀ (k l : ℕ) (w : Tape), slowOutput m p k l w ⊆ enumerated p [] [] w) ∧
    (∀ (k l t : ℕ) (v w : Tape), tapePrefix v t = tapePrefix w t →
      stageOutput p [] [] v t = stageOutput p [] [] w t ∧
      slowState m p k l t v = slowState m p k l t w) ∧
    (∀ (k l t j : ℕ) (F : Finset ℕ), 1 ≤ t → j ≤ 2 ^ (k + 2) →
      let b := collectLoop p k t j (scatterTable m p l t (history m p k l (t - 1)))
      tapeMeasure {w | eligible p t F (tapePrefix w t, lookup (tapePrefix w t) b) = true} =
        ENNReal.ofReal ((batchCount p t F b : ℝ) / (2 : ℝ) ^ t)) ∧
    Computable (fun z : ℕ × ℕ × ℕ =>
      Encodable.encode (history m p z.1 z.2.1 z.2.2)) ∧
    (∃ q : Machine, ∀ (k l : ℕ) (w : Tape),
      enumerated q [] (pairInput k l) w = slowOutput m p k l w) ∧
    (∀ (k l : ℕ) (S : Set ℕ), MeasurableSet {w | slowOutput m p k l w = S}) ∧
    (∀ (k l t : ℕ) (F : Finset ℕ), 1 ≤ t →
      collectable p k t F (history m p k l t) = false) := by sorry

end EnumeratingComplexity224.Dichotomy
