-- Prove2me | Theorems.Thm_EnumeratingComplexity224_Dichotomy_machine_foundations
-- name    : EnumeratingComplexity224.Dichotomy.machine_foundations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:28:16.915182+00:00
-- url     : https://prove2.me/theorems/902d3584-b812-4f69-b82e-da7d8746d7b6
-- title:
--   Definitions 7–10 — optimal machines and measurable output events
-- statement:
--   For the concrete effective machine model there exist optimal deterministic, randomized and conditional randomized machines, denoted $M,P,Q$. The deterministic comparison is additive in program length, the random comparison multiplicative in probability, and the conditional comparison uniform over all finite auxiliary strings.
--
--   For every code $A$, finite program $p$, auxiliary string $y$, and arbitrary $S\subseteq\mathbb N$, the exact-output event is measurable. Moreover every finite binary word $u$ defines a cylinder of its expected fair-coin mass:
--   $$\mu\{w:A(p,y,w)=S\}\text{ is a measurable-event probability},\qquad
--   \mu\{w:w\mathbin{\upharpoonright}|u|=u\}=2^{-|u|}.$$
--
--   These are foundational targets for existence and measurability; they do not assume any dichotomy or finite-witness statement. Only the three interfaces used by this mission are selected from the source's optimal-machine existence paragraph; conditional deterministic complexity is outside scope.
--
--   Differences from the source:
--   - encoding: Turing machines with finite padded binary inputs and non-halting output → finite partial-recursive instruction codes with padded cell reads, a sequential fair-bit interface and append-only natural-number messages; D takes values in the extended naturals and probabilities are extended nonnegative reals; reason: the interpreter gives effective finite simulations and the same infinite enumerations; program length is still the exact binary input length
-- source:
--   Alexander Shekhovtsov, Nikolay Vereshchagin, Georgii Zakharov, Enumerating Complexity Revisited, STOC 2027 submission #224 (October 2026), p. 5–6, footnote 1 and existence paragraph after Definition 10

import Definitions.Def_EnumeratingComplexity224_Dichotomy_Machines

namespace EnumeratingComplexity224.Dichotomy

/-- Definitions 7–10 and footnote 1, pp.5–6. -/
theorem machine_foundations :
    (∃ m p q : Machine, OptimalDeterministic m ∧ OptimalRandom p ∧ OptimalConditional q) ∧
    (∀ (a : Machine) (p y : Word) (S : Set ℕ),
      MeasurableSet {w : Tape | enumerated a p y w = S}) ∧
    (∀ u : Word, tapeMeasure {w | (List.range u.length).map w = u} =
      ENNReal.ofReal (dyadic u.length)) := by sorry

end EnumeratingComplexity224.Dichotomy
