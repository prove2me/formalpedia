-- Prove2me | Theorems.Thm_EnumeratingComplexity224_Dichotomy_conditioning_domination
-- name    : EnumeratingComplexity224.Dichotomy.conditioning_domination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:28:32.537438+00:00
-- url     : https://prove2.me/theorems/96a06c28-cbc7-4961-bfca-534588978d83
-- title:
--   Lemma 12(a) — uniform domination when conditioning
-- statement:
--   Fix an optimal randomized machine defining $R(S)$ and an optimal conditional randomized machine defining $R(S\mid y)$. There is a positive real constant $c$, depending only on these fixed choices, such that for every $S\subseteq\mathbb N$ and every finite binary string $y$,
--   $$R(S\mid y)\ge cR(S).$$
--   The same $c$ works for all sets and all auxiliary inputs. This is the whole labelled part (a), including its universal preamble and positivity; parts (b) and (c) are separate results and are not claimed here. The preamble's unused variable $k$ does not occur in part (a), so it is omitted from the binder list without changing its content. This comparison also applies when $S$ is finite or has probability zero.
--
--   Differences from the source:
--   - encoding: Turing machines with finite padded binary inputs and non-halting output → finite partial-recursive instruction codes with padded cell reads, a sequential fair-bit interface and append-only natural-number messages; D takes values in the extended naturals and probabilities are extended nonnegative reals; reason: the interpreter gives effective finite simulations and the same infinite enumerations; program length is still the exact binary input length
--   - generalization: fixed optimal machines and the p.6 convention D(S)>0 and R(S)≤1/4 when using logarithmic bounds → arbitrary fixed optimal machines, without the logarithmic normalization; reason: the p.6 convention sets aside finitely many exceptional sets to make logarithms defined; the selected logarithm-free source arguments apply to all optimal machine choices and all their sets
--   - encoding: the universal preamble also quantifies an unused natural k → the binder k is omitted from part (a); reason: the formula is independent of k and the natural numbers are inhabited
-- source:
--   Alexander Shekhovtsov, Nikolay Vereshchagin, Georgii Zakharov, Enumerating Complexity Revisited, STOC 2027 submission #224 (October 2026), p. 6, Lemma 12(a)

import Definitions.Def_EnumeratingComplexity224_Dichotomy_Machines

namespace EnumeratingComplexity224.Dichotomy

/-- Complete labelled Lemma 12(a), p.6. The unused source variable k is omitted. -/
theorem conditioning_domination (p q : Machine)
    (hp : OptimalRandom p) (hq : OptimalConditional q) :
    ∃ c : ℝ, 0 < c ∧ ∀ (S : Set ℕ) (y : Word),
      ENNReal.ofReal c * probability p S [] ≤ probability q S y := by sorry

end EnumeratingComplexity224.Dichotomy
