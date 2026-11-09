-- Prove2me | Theorems.Thm_EnumeratingComplexity224_Dichotomy_not_all_eventually_free
-- name    : EnumeratingComplexity224.Dichotomy.not_all_eventually_free
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:33:50.466291+00:00
-- url     : https://prove2.me/theorems/038a1ed1-ae00-4324-a63a-14438bb7604a
-- title:
--   Lemma 16 — not all good slow ants are eventually free
-- statement:
--   Fix optimal deterministic and randomized machines, natural parameters $k,l$, and an infinite set $S\subseteq\mathbb N$ with $R(S)\ge2^{-k}$. A tape is good when the fast machine's entire output equals $S$. In the specific slow process there is a good tape which is not eventually free:
--   $$\exists w,\quad P(w)=S\quad\text{and}\quad w\text{ is not in case C}.$$
--   Here case C means that from some stage on the slow row is free with no release or collecting transitions. The result uses the full infinite tape space and imposes no computable-enumerability assumption on $S$. The unnumbered trichotomy immediately preceding Lemma 16 is part of the process background, not a second numbered lemma. This milestone supplies the source's nonemptiness conclusion about good tapes outside case C.
--
--   Differences from the source:
--   - encoding: Turing machines with finite padded binary inputs and non-halting output → finite partial-recursive instruction codes with padded cell reads, a sequential fair-bit interface and append-only natural-number messages; D takes values in the extended naturals and probabilities are extended nonnegative reals; reason: the interpreter gives effective finite simulations and the same infinite enumerations; program length is still the exact binary input length
--   - generalization: fixed optimal machines and the p.6 convention D(S)>0 and R(S)≤1/4 when using logarithmic bounds → arbitrary fixed optimal machines, without the logarithmic normalization; reason: the p.6 convention sets aside finitely many exceptional sets to make logarithms defined; the selected logarithm-free source arguments apply to all optimal machine choices and all their sets
--   - encoding: any eligible collecting choice in the stage process of §3.1 → least finite-set binary code among all subsets of the finite fast-output union, with 2^(k+2) collecting attempts and identity attempts after exhaustion; reason: this is a computable permitted tie-break; the source proves at most 2^(k+2) successful iterations
--   - reading: cases A, B and C refer to moments throughout the scattering/collecting process → release and collecting event flags are retained within each stage; case B forbids every later release, even when refreezing occurs in that stage; reason: p.9 explicitly allows two transitions in one stage and the proof of Lemma 18 requires continuous freezing, not just frozen stage endpoints
-- source:
--   Alexander Shekhovtsov, Nikolay Vereshchagin, Georgii Zakharov, Enumerating Complexity Revisited, STOC 2027 submission #224 (October 2026), p. 9, Lemma 16 with §3 preamble, p.7

import Definitions.Def_EnumeratingComplexity224_Dichotomy_Process

namespace EnumeratingComplexity224.Dichotomy

/-- Lemma 16, p.9, with the infinite-set setup of §3. -/
theorem not_all_eventually_free (m p : Machine)
    (hm : OptimalDeterministic m) (hp : OptimalRandom p)
    (k l : ℕ) (S : Set ℕ) (hS : S.Infinite)
    (hR : ENNReal.ofReal (dyadic k) ≤ probability p S []) :
    ∃ w : Tape, enumerated p [] [] w = S ∧ ¬caseC m p k l w := by sorry

end EnumeratingComplexity224.Dichotomy
