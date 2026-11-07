-- Prove2me | Theorems.Thm_BoolCSPDel_theorem_4_3
-- name    : BoolCSPDel.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:55:38.450207+00:00
-- url     : https://prove2.me/theorems/1ad1f1c4-f9ae-4b82-bbea-8fdb11caf35d
-- title:
--   Theorem 4.3 — strict-turnstile streaming to sketching ([JLY26], cited)
-- statement:
--   Fix $k$ and an integer $F\ge1$. There is a constant $c_s$ such that any randomized $S$-bit one-pass algorithm deciding $\mathrm{CSP}(\Gamma)$ with error at most $1/3$ on every strict-turnstile stream of length at most $n^{c_s}$ yields a public-coin linear sketch with the same error on every instance in $\{0,\dots,F\}^{U}$ and of size $O_{k,F}(S\log(S+2))$, for all large $n$.
--
--   This transfer lets the sketching lower bound apply to streaming algorithms.
--
--   **Formalization Note** The theorem is cited from Jiang, Liu and Yu, whose paper was not in hand; the statement rests on this paper's text. The algorithm model is the automaton with a free persistent seed.
--
--   Differences from the source:
--   - generalization: one relation R → a language Γ of relations of arity at most k; reason: p.29 says the result applies to the universe U^Γ_n; Γ = {R} is the printed case
--   - reading: "any randomized S-bit one-pass algorithm", no model named → TurnstileAlg with a free persistent seed, S = log₂ of the state count; reason: the model of the transfer as read from this paper; [JLY26] was not in hand
--   - encoding: success with probability at least 2/3 → CosDensity.SucceedsWP: a measurable event of measure at least 2/3 inside the success set; reason: an inner-measure lower bound; for measurable success sets it is the same
--   - encoding: O_{k,F} and c_{R,F}, for fixed R and F → c_s, N₀, C chosen for k and F before Γ; reason: finitely many languages of arity at most k (p.17)
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), Theorem 4.3, p.24; proof of Corollary 4.15, p.29

import Mathlib
import Definitions.Def_BoolCSPDel_degZ
import Definitions.Def_BoolCSPDel_Con
import Definitions.Def_BoolCSPDel_TurnstileAlg
import Definitions.Def_BoolCSPDel_Sketch
import Definitions.Def_CosDensity_StreamAlg

open MeasureTheory

namespace BoolCSPDel

/-- **Theorem 4.3 (strict-turnstile streaming to sketching, cited from [JLY26]).** Bandekar, Sharma, Velusamy, *A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions*, STOC 2027 submission (manuscript sha256 15f83519…), Theorem 4.3,
p.24, in the language form of p.29 ("applies to the universe `U^Γ_n`").

An `S`-bit algorithm deciding `CSP(Γ)` with error at most `1/3` on every strict-turnstile stream of length
at most `n^{c_s}` yields a public-coin linear sketch with the same error on every instance in
`{0, …, F}^U`, of size `O_{k,F}(S log(S + 2))`, for all large `n`.

**Formalization Note.** Standing assumption of §3.1, p.18, carried over: nonempty proper relations, not
constant-satisfiable. The algorithm model is `TurnstileAlg`. [JLY26] was not in hand; the statement rests
on this paper's text. -/
theorem theorem_4_3 (k F : ℕ) (hF : 1 ≤ F) : ∃ (c_s N₀ : ℕ) (C : ℝ), 0 < C ∧
    ∀ Γ : Lang k, AllNonemptyProper Γ → ¬ ConstSat Γ → ∀ n, N₀ ≤ n →
      ∀ (Ω St : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] [Fintype St]
        (A : TurnstileAlg (Con Γ (Fin n)) Ω St Bool),
        (∀ s : List (Con Γ (Fin n) × Bool), IsLegal s → s.length ≤ n ^ c_s →
          CosDensity.SucceedsWP μ
            (fun ω => A.out ω (A.run ω s) = true ↔ (Sat (freq s)).Nonempty) (2 / 3)) →
        ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω') (_ : IsProbabilityMeasure μ')
          (σ : Sketch (Con Γ (Fin n)) Ω' Bool) (B : ℝ),
          (∀ f : Con Γ (Fin n) → ℤ, (∀ C, 0 ≤ f C ∧ f C ≤ F) →
            CosDensity.SucceedsWP μ' (fun ω => σ.out ω f = true ↔ (Sat f).Nonempty) (2 / 3)) ∧
          σ.HasSize B ∧
          B ≤ C * CosDensity.memoryBits St * Real.log (CosDensity.memoryBits St + 2) := by sorry

end BoolCSPDel
