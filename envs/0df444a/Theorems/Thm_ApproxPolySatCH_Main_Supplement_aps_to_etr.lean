-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_Supplement_aps_to_etr
-- name    : ApproxPolySatCH.Main.Supplement.aps_to_etr
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T04:55:52.147726+00:00
-- url     : https://prove2.me/theorems/6468206f-dd8d-4df8-b7a0-a65cdbf3b5fa
-- title:
--   Theorem 16 — Rational APS reduces to the existential theory of the reals
-- statement:
--   For polynomial tuples with rational coefficients, approximate polynomial satisfiability is deterministic polynomial-time many-one reducible to truth of existential sentences over the reals:
--   $$\mathrm{APS}_{\mathbb Q}\leq_m^{\mathrm P}\mathrm{ETR}.$$
--   The source language is the published rational APS language with sparse, dense and division-free circuit input tags. The target is the explicit binary language of true existential sentences in the signature $(0,1,+,\cdot,<)$ with equality and arbitrary Boolean combinations. Thus there are a single finite deterministic program, a total output function $r$ and constants $c,d\in\mathbb N$ such that the program outputs $r(w)$ within $c(|w|+1)^d$ steps on every binary word $w$, and
--   $$w\in\mathrm{APS}_{\mathbb Q}\iff r(w)\in\mathrm{ETR}.$$
--   No input norm bound, attained infimum, exact common zero, separation estimate, or semialgebraic oracle is assumed. In particular, approximate zeros escaping to infinity remain included. Malformed source and target words are no instances of their respective languages.
--
--   This companion theorem gives the characteristic-zero relation to real feasibility. It concerns one output existential sentence, preserving the strength of the source's construction, and does not assert finite-field ETR semantics.
--
--   Differences from the source:
--   - reading: APS_Q is "polynomial-time reducible" to ETR, reduction type unstated → ManyOneReduction, a deterministic polynomial-time many-one reduction; reason: the proof outputs one existential sentence that is true iff the instance is positive, so the many-one reading is what the proof establishes, and it implies the Turing reading
--   - generalization: APS_Q with the default sparse encoding (§3, p.14: "Unless otherwise stated, polynomials are represented sparsely") → the published tagged APSLanguage .rational, which also accepts dense and division-free circuit inputs; reason: the three tags are disjoint, so composing with w ↦ [false,false] ++ w gives exactly a reduction from SparseLanguage .rational, the source's claim; §3 states the three encodings are polynomial-time equivalent
--   - encoding: ETR, true existential sentences over (0,1,+,*,<) interpreted over a real closed field → ETRLanguage, length-delimited binary codes of finite existential sentences with equality and strict-order atoms and ¬, ∧, ∨, interpreted over ℝ; reason: ℝ is real closed and the theory of real closed fields is complete, so truth of a parameter-free sentence is the same in every real closed field; equality is the logical equality of first-order logic
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), Theorem 16, p.28 (PDF p.28), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=28

import Definitions.Def_ApproxPolySatCH_Main_Supplement_ExistentialReals

set_option autoImplicit false

namespace ApproxPolySatCH.Main.Supplement

/-- Theorem 16, p.28: the proof outputs one existential sentence, on all input encodings. -/
theorem aps_to_etr :
    ManyOneReduction (APSLanguage .rational) ETRLanguage := by sorry

end ApproxPolySatCH.Main.Supplement
