-- Prove2me | Theorems.Thm_ContractionLemma_Supplement_theorem_10_exact_classical_simulation
-- name    : ContractionLemma.Supplement.theorem_10_exact_classical_simulation
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:26:29.294861+00:00
-- url     : https://prove2.me/theorems/a1a79efc-053a-4f95-acf7-a132c4294c84
-- title:
--   Theorem 10, p.36 — the numbers of accepting coin strings and of accepting paths of a $T$-step machine in time $\mathrm{poly}(T+L)2^{O(T/\sqrt{\log T})}$
-- statement:
--   Fix the parameters of local machines: $k$ tapes, an alphabet $\Gamma$, a head-movement bound $d_0$ and a constant $C_0$. Given a program $M$ with at most $(T+2)^{C_0}$ states, its input and auxiliary words and a time bound $T\ge2$, with description length $L$, the following can be computed deterministically in time $\mathrm{poly}(T+L)\,2^{O(T/\sqrt{\log T})}$ and polynomial space:
--
--   1. the number of accepting coin strings $A$, so that $\Pr[\text{accept by time }T]=2^{-T}A$;
--   2. the number of accepting nondeterministic paths.
--
--   The bounds are $C(T+L+1)^C\,2^{CT/\sqrt{\log_2(T+2)}}$ in time and $C(T+L+1)^C$ in space, $C$ depending only on $(k,\Gamma,d_0,C_0)$. This exact simulation underlies all the separations of Part II.
--
--   Differences from the source:
--   - reading: no space bound in the theorem sentence → space at most $C(T+L+1)^C$; reason: the convention of p.3; the proof (p.37) says "so the space is polynomial"
--   - encoding: local machines of §2.5 → alphabet $\mathrm{Fin}(\gamma+3)$ with blank and bits fixed; acceptance means an accepting halting state at time $T$; oracle states, if any, answered $0$; reason: Lean model of §2.5; halting states are absorbing
--   - encoding: $O(\cdot)$, $\mathrm{poly}(\cdot)$, $E(u)=2^{O(u/\sqrt{\log u})}$ → explicit constants fixed before the instance; $E(u)=2^{C f(u)}$, $f(u)=u/\sqrt{\log_2(u+2)}$; reason: the paper's own $f$ (p.16); log base two
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Theorem 10, p.36 (stated first on p.8); §2.5, p.20; proof p.37

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_RunsWithin
import Definitions.Def_ContractionLemma_Supplement_Common
import Definitions.Def_ContractionLemma_Supplement_LocalMachine

set_option autoImplicit false

namespace ContractionLemma.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- **Theorem 10 (Exact classical simulation)** — Gajulapalli, *The Contraction Lemma Beyond ETH*
(manuscript, sha256 049caea1…), p.36 (PDF p.39; stated first on p.8).

"For a given machine with time bound `T` and description length `L`, the number of accepting coin
strings, and the number of accepting nondeterministic paths, can be computed in time
`poly(T + L) 2^{O(T/√log T)}`."

For every choice of the fixed parameters `(k, Γ, d₀, C₀)` of §2.5 there are machines and a constant
`C` such that, for every program `M` with at most `(T+2)^{C₀}` states, every input word `x`,
auxiliary word `aux` and time bound `T ≥ 2`, given `(M, x, aux, T)` (length `L`), one outputs the
number of accepting coin strings and the other the number of accepting nondeterministic paths of the
run for `T` steps, in time `C (T+L+1)^C 2^{C f(T)}` and space `C (T+L+1)^C`.

**Formalization Note.** The program is part of the input (`LProgram.encode`); the algorithm is
uniform over all programs with these parameters. `f(T) = T/√log₂(T+2)`. Oracle states, if any, are
answered `0` (no oracle). The polynomial-space clause is the paper's convention (p.3), and the proof
(p.37) states it. -/
theorem theorem_10_exact_classical_simulation (p : LocalParams) :
    (∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ),
      ∀ (M : LProgram p) (x aux : List Bool) (T : ℕ), 2 ≤ T → M.Q ≤ (T + 2) ^ p.C0 →
        ContractionLemma.RunsWithin A out (M.simInput x aux T)
          (countWord (M.coinCount (fun _ => False) x aux T))
          (C * ((T : ℝ) + (M.simInput x aux T).length + 1) ^ C * (2 : ℝ) ^ (C * fScale T))
          (C * ((T : ℝ) + (M.simInput x aux T).length + 1) ^ C)) ∧
    (∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ),
      ∀ (M : LProgram p) (x aux : List Bool) (T : ℕ), 2 ≤ T → M.Q ≤ (T + 2) ^ p.C0 →
        ContractionLemma.RunsWithin A out (M.simInput x aux T)
          (countWord (M.pathCount (fun _ => False) x aux T))
          (C * ((T : ℝ) + (M.simInput x aux T).length + 1) ^ C * (2 : ℝ) ^ (C * fScale T))
          (C * ((T : ℝ) + (M.simInput x aux T).length + 1) ^ C)) := by sorry

end ContractionLemma.Supplement
