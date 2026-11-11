-- Prove2me | Theorems.Thm_EditPRC_Boost_proposition_3_15
-- name    : EditPRC.Boost.proposition_3_15
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:08:43.890031+00:00
-- url     : https://prove2.me/theorems/a652a8f8-525d-43cc-82f6-7d76291cebf6
-- title:
--   Proposition 3.15 — self-matching is checkable in time $O(n^2)$; a string whose check has advantage $a$ is self-matching with probability $\ge 1-2^{-\varepsilon n}-a$
-- statement:
--   Let $\Gamma$ be a finite alphabet.
--
--   1. **Checking in time $O(n^2)$.** There is a constant $C$ such that for every real $\varepsilon$ some program of the unit-cost real RAM decides, for every $n$ and every $s\in\Gamma^n$ written into its memory, whether $s$ is $\varepsilon$-self-matching, halting within
--   $$C\,n^2 + C \ \text{steps}.$$
--   2. **Pseudorandom strings.** If $|\Gamma|\ge2e^2\varepsilon^{-2}$, then for every $n$, every probability distribution $\mu$ on $\Gamma^n$ and every $a$ such that the probability of the event "$\varepsilon$-self-matching" under $\mu$ is within $a$ of its probability under the uniform distribution,
--   $$\Bigl|\Pr_\mu[\varepsilon\text{-SM}]-\Pr_{\mathrm{Unif}}[\varepsilon\text{-SM}]\Bigr|\le a\ \Longrightarrow\ \Pr_\mu[\varepsilon\text{-SM}]\ \ge\ 1-2^{-\varepsilon n}-a .$$
--   In the paper $a=1/f(\lambda)$ is the advantage of the checking algorithm of part 1 used as a distinguisher.
--
--   Part 1 makes self-matching an efficiently testable property, so part 2 transfers Proposition 3.14 from random to pseudorandom synchronization strings in the proof of Theorem 3.12.
--
--   Differences from the source:
--   - reading: "an algorithm ... in time $O(n^2)$" → a program of the published unit-cost real RAM `SmaleNinth_RealRAM` (each instruction, memory access and comparison costs one step; real constants such as $\varepsilon$ allowed), input $M[0]=n$, $M[1+i]=1+\mathrm{index}(s_i)$, accepting exactly the $\varepsilon$-self-matching strings within $Cn^2+C$ steps, $C$ depending only on $\Gamma$; reason: the dynamic program of the proof has $n^2$ cells with $O(1)$ work each in a unit-cost model, which is how the bound is meant.
--   - generalization: "a pseudorandom string with advantage difference $1/f(\lambda)$" → any distribution $\mu$ on $\Gamma^n$ whose probability of the self-matching event is within $a$ of the uniform one, any real $a$; reason: weaker hypothesis; a string with advantage at most $1/f(\lambda)$ against efficient distinguishers in particular has it against the checking algorithm of part 1 (the paper's proof uses only that distinguisher), so the statement specializes to the source's with $a=1/f(\lambda)$.
--   - encoding: distributions → `PMF (Fin n → Γ)`, probabilities as real numbers; reason: Lean convention.
--   - generalization: $\varepsilon>0$ (implicit) → any real $\varepsilon$; reason: for $\varepsilon\le0$ part 1 asks for a checker that always rejects and part 2 is trivially true, so on $\varepsilon>0$ the statement is the source's.
--
--   **Formalization Note.** No sign condition on $\varepsilon$ is imposed: for $\varepsilon\le0$ no string is $\varepsilon$-self-matching and part 2 is trivial.
-- source:
--   Gozon, Edit-Robust Pseudorandom Codes, Watermarks, and Steganography, STOC 2027 submission (manuscript sha256 73170029…6b60), p. 25, Proposition 3.15 (and its proof)

import Mathlib
import Definitions.Def_EditPRC_Boost_Machine
import Definitions.Def_EditPRC_Boost_SelfMatching

namespace EditPRC.Boost

/-- **Proposition 3.15.** (1) For every finite alphabet `Γ` there is a constant `C` such that for
every `ε` some unit-cost real-RAM program decides, on every `s ∈ Γ^n`, whether `s` is
`ε`-self-matching within `C n² + C` steps. (2) If `|Γ| ≥ 2e²ε^{−2}` and a distribution `μ` on
`Γ^n` gives the event "`ε`-self-matching" a probability within `a` of its probability under the
uniform distribution (the advantage of the checking algorithm is at most `a = 1/f(λ)`), then
under `μ` the string is `ε`-self-matching with probability at least `1 − 2^{−εn} − a`. -/
theorem proposition_3_15 :
    (∀ (Γ : Type) [Fintype Γ], ∃ C : ℕ, ∀ ε : ℝ, ∃ R : SmaleNinth.RAMProgram,
      ∀ (n : ℕ) (s : Fin n → Γ), ∃ b : Bool,
        SmaleNinth.RAMDecidesInTime R (ramInput1 s) (C * n ^ 2 + C) b ∧
        (b = true ↔ IsSelfMatching ε s)) ∧
    (∀ (Γ : Type) [Fintype Γ] (ε : ℝ),
      2 * Real.exp 2 * ε ^ (-2 : ℤ) ≤ (Fintype.card Γ : ℝ) →
      ∀ (n : ℕ) (μ : PMF (Fin n → Γ)) (a : ℝ),
        |(μ.toOuterMeasure {s | IsSelfMatching ε s}).toReal -
            unifProb (fun s : Fin n → Γ => IsSelfMatching ε s)| ≤ a →
        1 - (2 : ℝ) ^ (-(ε * n)) - a ≤ (μ.toOuterMeasure {s | IsSelfMatching ε s}).toReal) := by sorry

end EditPRC.Boost
