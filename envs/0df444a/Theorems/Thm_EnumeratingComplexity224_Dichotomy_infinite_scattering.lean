-- Prove2me | Theorems.Thm_EnumeratingComplexity224_Dichotomy_infinite_scattering
-- name    : EnumeratingComplexity224.Dichotomy.infinite_scattering
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:35:21.77697+00:00
-- url     : https://prove2.me/theorems/ec9ca501-5cf2-4d73-a890-4c31db697795
-- title:
--   Lemma 17 — a good tape with infinitely many releases
-- statement:
--   Fix optimal deterministic and randomized machines, natural $k,l$, and an infinite $S\subseteq\mathbb N$ with $R(S)\ge2^{-k}$. Suppose there is a good tape whose slow copy is released arbitrarily late in the constructed process, which is case A. Then
--   $$D(S)\le l.$$
--   Goodness means that the fast machine's complete output equals $S$. Release events include a release and refreezing within the same stage. Infinitely many releases also entail infinitely many collecting transitions for this process. The conclusion is about an exact deterministic enumeration of all of $S$, rather than a sequence of finite approximations with changing programs.
--
--   Differences from the source:
--   - encoding: Turing machines with finite padded binary inputs and non-halting output → finite partial-recursive instruction codes with padded cell reads, a sequential fair-bit interface and append-only natural-number messages; D takes values in the extended naturals and probabilities are extended nonnegative reals; reason: the interpreter gives effective finite simulations and the same infinite enumerations; program length is still the exact binary input length
--   - generalization: fixed optimal machines and the p.6 convention D(S)>0 and R(S)≤1/4 when using logarithmic bounds → arbitrary fixed optimal machines, without the logarithmic normalization; reason: the p.6 convention sets aside finitely many exceptional sets to make logarithms defined; the selected logarithm-free source arguments apply to all optimal machine choices and all their sets
--   - encoding: any eligible collecting choice in the stage process of §3.1 → least finite-set binary code among all subsets of the finite fast-output union, with 2^(k+2) collecting attempts and identity attempts after exhaustion; reason: this is a computable permitted tie-break; the source proves at most 2^(k+2) successful iterations
--   - reading: cases A, B and C refer to moments throughout the scattering/collecting process → release and collecting event flags are retained within each stage; case B forbids every later release, even when refreezing occurs in that stage; reason: p.9 explicitly allows two transitions in one stage and the proof of Lemma 18 requires continuous freezing, not just frozen stage endpoints
-- source:
--   Alexander Shekhovtsov, Nikolay Vereshchagin, Georgii Zakharov, Enumerating Complexity Revisited, STOC 2027 submission #224 (October 2026), p. 10, Lemma 17 with §3 preamble, p.7

import Definitions.Def_EnumeratingComplexity224_Dichotomy_Process

namespace EnumeratingComplexity224.Dichotomy

/-- Lemma 17, p.10: actual release events, including release/refreeze. -/
theorem infinite_scattering (m p : Machine)
    (hm : OptimalDeterministic m) (hp : OptimalRandom p)
    (k l : ℕ) (S : Set ℕ) (hS : S.Infinite)
    (hR : ENNReal.ofReal (dyadic k) ≤ probability p S [])
    (hA : ∃ w : Tape, enumerated p [] [] w = S ∧ caseA m p k l w) :
    complexity m S ≤ (l : ℕ∞) := by sorry

end EnumeratingComplexity224.Dichotomy
