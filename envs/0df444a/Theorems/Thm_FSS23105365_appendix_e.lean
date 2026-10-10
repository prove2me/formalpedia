-- Prove2me | Theorems.Thm_FSS23105365_appendix_e
-- name    : FSS23105365.appendix_e
-- status  : Proved
-- author  : @YY
-- created : 2026-10-09T16:08:55.605785+00:00
-- url     : https://prove2.me/theorems/6cc22627-5ced-411d-8793-47277fb72c91
-- title:
--   Appendix E — all six finite-state sampling results
-- statement:
--   This goal is the conjunction of all six numbered statements E.1–E.6 of Appendix E, with the linear seed guarantee accompanying E.5 recorded as a seventh conjunct. It is an organizational completion condition for this mission, not an additional numbered theorem attributed to the paper.
--
--   For every fixed binary DFA or finite real-valued Markov chain, as appropriate, establish all of the following:
--
--   1. **E.1:** exactly sample a uniform length-$n$ word together with its acceptance bit, using exactly $n$ fair bits and polynomial-size constant-depth circuits.
--   2. **E.2:** whenever the accepted length-$n$ slice is nonempty, sample its uniform law to total variation error at most $\epsilon$, with every output accepted, using at most $n+C\log_2(1/\epsilon)$ fair bits, polynomial size in $n+1$ and $1/\epsilon$, and depth independent of both parameters.
--   3. **E.3:** represent every transition-dyadic chain as a fixed projection of the run of one binary DFA on a uniform word of length $v+ns$, observed at times $v,v+s,\ldots,v+ns$, for fixed positive integers $v,s$.
--   4. **E.4:** lift every path-dyadic chain to a finite chain with dyadic initial and transition entries, preserving every complete trajectory law under a fixed coordinatewise projection.
--   5. **E.5:** exact polynomial-size constant-depth fair-bit sampling of all complete trajectories is equivalent to dyadicity of every finite path probability.
--   6. **E.5 seed guarantee:** whenever this condition holds, the exact sampler needs at most $C(n+1)$ fair bits.
--   7. **E.6:** for every terminal set $F$ with positive acceptance probability, sample the full trajectory conditioned on $X_n\in F$ within total variation $\epsilon$, using at most $C(n+\log_2(1/\epsilon))$ fair bits, polynomial size and constant depth; every output has positive conditional probability.
--
--   The approximation range is $0<\epsilon\le1/2$. All length quantifiers include zero. Each result has its own constants, quantified before length and accuracy; in E.6 these constants also precede the accepting set. Path-dyadicity includes initial probabilities through length-zero paths. Transition-dyadicity includes both initial and transition entries. Circuit families are nonuniform existential families built from explicit Boolean gates; the statements assert no efficient procedure for computing circuit descriptions from real input probabilities.
--
--   The mission is complete only when all these conjuncts are proved. In particular proving only E.5 does not prove this goal.
-- source:
--   Jiarui Zhang, Chengwei Liang, Haozhe Jiang, Binhang Yuan, Jingzhao Zhang. Revision Provably Reduces Sequential Computation in Diffusion Language Models. https://doi.org/10.5281/zenodo.23105365, Appendix E. Theorems E.1, E.2, E.5, E.6; Lemmas E.3 and E.4; E.1 motivation third bullet for the E.5 seed bound.

import Definitions.Def_FSS23105365_DFARun
set_option autoImplicit false
open FSS23105365

theorem FSS23105365.appendix_e :
    (∀ (q : ℕ) (A : BinaryDFA q),
      ∃ D C k : ℕ, ∀ n : ℕ, ∃ S : Circuit (Option (Fin n)),
        S.randomBits = n ∧ S.depth ≤ D ∧ S.size ≤ C * (n + 1) ^ k ∧
        ExactLaw S pairOutcomeEncode (pairLaw A)) ∧
    (∀ (q : ℕ) (A : BinaryDFA q),
      ∃ D C k : ℕ, ∀ n : ℕ, (acceptedWords A n).Nonempty →
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ S : Circuit (Fin n),
          S.depth ≤ D ∧
          (S.size : ℝ) ≤ (C : ℝ) * (((n + 1 : ℕ) : ℝ) / ε) ^ k ∧
          (S.randomBits : ℝ) ≤ (n : ℝ) + (C : ℝ) * logInv ε ∧
          SupportPreserving S (fun x : Bits n => x) (wordLaw A) ∧
          tv (mass S (fun x : Bits n => x)) (wordLaw A) ≤ ε) ∧
    (∀ {q : ℕ} (M : MarkovChain q), TransitionDyadic M →
      ∃ r : ℕ, ∃ B : BinaryDFA r, ∃ v s : ℕ, 0 < v ∧ 0 < s ∧
        ∃ φ : Fin r → Fin q, ∀ n : ℕ, ∀ γ : Path q n,
          (Fintype.card {x : Bits (v + n * s) // B.sampledPath φ v s x = γ} : ℝ) /
            2 ^ (v + n * s) = pathLaw M γ) ∧
    (∀ (q : ℕ), 0 < q → ∀ (M : MarkovChain q), PathDyadic M →
      ∃ r : ℕ, 0 < r ∧ ∃ N : MarkovChain r, ∃ φ : Fin r → Fin q,
        TransitionDyadic N ∧
        ∀ n : ℕ, ∀ γ : Path q n, projectedPathLaw N φ γ = pathLaw M γ) ∧
    (∀ (q : ℕ), 0 < q → ∀ (M : MarkovChain q), ExactPathAC0 M ↔ PathDyadic M) ∧
    (∀ (q : ℕ), 0 < q → ∀ (M : MarkovChain q), PathDyadic M →
      ∃ D C k : ℕ, ∀ n : ℕ, ∃ S : Circuit (Fin (n + 1) × Fin q),
        S.depth ≤ D ∧ S.size ≤ C * (n + 1) ^ k ∧
        S.randomBits ≤ C * (n + 1) ∧ ExactLaw S pathEncode (pathLaw M)) ∧
    (∀ (q : ℕ), 0 < q → ∀ (M : MarkovChain q),
      ∃ D C k : ℕ, ∀ F : Finset (Fin q), ∀ n : ℕ,
        0 < acceptanceProbability M F n →
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ∃ S : Circuit (Fin (n + 1) × Fin q),
          S.depth ≤ D ∧
          (S.size : ℝ) ≤ (C : ℝ) * (((n + 1 : ℕ) : ℝ) / ε) ^ k ∧
          (S.randomBits : ℝ) ≤ (C : ℝ) * ((n : ℝ) + logInv ε) ∧
          SupportPreserving S pathEncode (conditionedPathLaw M F) ∧
          tv (mass S pathEncode) (conditionedPathLaw M F) ≤ ε) := by sorry
