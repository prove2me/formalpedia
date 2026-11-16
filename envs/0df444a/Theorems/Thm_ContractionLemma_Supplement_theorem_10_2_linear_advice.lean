-- Prove2me | Theorems.Thm_ContractionLemma_Supplement_theorem_10_2_linear_advice
-- name    : ContractionLemma.Supplement.theorem_10_2_linear_advice
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:29:47.390376+00:00
-- url     : https://prove2.me/theorems/c3962c4c-a7b0-402d-921a-b706ae6941c7
-- title:
--   Theorem 10.2, p.41 — a language decidable in time $2^{o(n)}$ and polynomial space outside $i.o.\text{-}\mathcal C^{cl}_t/n$
-- statement:
--   Let $\mathcal C^{cl}_t=\mathsf{BPTIME}[t]\cup\mathsf{NTIME}[t]\cup\mathsf{coNTIME}[t]\cup\mathsf{PPTIME}[t]\cup\oplus\mathsf{TIME}[t]$. For every time-constructible $t$ in the range (1) there is a language $L$ such that
--
--   1. $L$ is decidable deterministically in time $2^{o(n)}$ and space $\mathrm{poly}(n)$;
--   2. if $t(n)=n$, $L$ is decidable deterministically in time $2^{O(n\log\log n/\sqrt{\log n})}$ and space $\mathrm{poly}(n)$;
--   3. $L\notin i.o.\text{-}\mathcal C^{cl}_t/n$: every fixed machine of these classes, with any advice of length at most $n$, errs on some input at every sufficiently large length.
--
--   The hard language is thus far below exponential time while defeating near-linear-time machines with linear advice.
--
--   Differences from the source:
--   - reading: $\log\log n$ → $\log_2(\log_2(n+2)+2)$; reason: agrees with $\log\log n$ up to an additive constant and has no junk values at small $n$
--   - encoding: time $2^{o(n)}$ → time $C\,2^{g(n)}$ for some $g$ with $g(n)/n\to0$; reason: explicit function for the $o(\cdot)$
--   - encoding: time $O(t)$ (clocks $c\,t(n)$, at most $c\,t(n)$ gates, ancillas and witness bits; time-constructibility within $O(t(n))$ steps) → $c\,(t(n)+1)$; reason: equal to $c\,t(n)$ up to the constant for $n\ge1$, since $t(n)\ge n\ge1$; at $n=0$ it avoids the junk bound $0$, under which no machine halts and $t(n)=n$ would not be time-constructible
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Theorem 10.2, p.41; Definition 2.10, p.21

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_ContractionLemma_RunsWithin
import Definitions.Def_ContractionLemma_Supplement_Common
import Definitions.Def_ContractionLemma_Supplement_LocalMachine
import Definitions.Def_ContractionLemma_Supplement_Quantum
import Definitions.Def_ContractionLemma_Supplement_Classes

set_option autoImplicit false

namespace ContractionLemma.Supplement

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
open scoped Classical
/-- **Theorem 10.2 (Linear advice)** — Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript,
sha256 049caea1…), p.41 (PDF p.44).

"Let `C^cl_t = BPTIME[t] ∪ NTIME[t] ∪ coNTIME[t] ∪ PPTIME[t] ∪ ⊕TIME[t]`. For every
time-constructible `t` in the range (1), there is a language `L` decidable deterministically in time
`2^{o(n)}` and space `poly(n)` such that `L ∉ i.o.-C^cl_t/n`. That is, every fixed machine of these
classes, with any advice of length at most `n`, errs on some input at every sufficiently large length.
For `t(n) = n` the time is `2^{O(n log log n/√log n)}`."

For every `t` in the range (1) there is a language `L` such that:

1. for some `g` with `g(n)/n → 0`, a machine decides `L` in time `C 2^{g(n)}` and space `C (n+1)^C`;
2. if `t(n) = n` for all `n`, a machine decides `L` in time
   `C 2^{C n log₂(log₂(n+2)+2)/√log₂(n+2)}` and space `C (n+1)^C`;
3. `L ∉ i.o.-C^cl_t/n`.

**Formalization Note.** Deciding means outputting the one-bit word `[x ∈ L]`. `log log n` is read
as `log₂(log₂(n+2)+2)`, which agrees with it up to an additive constant. -/
theorem theorem_10_2_linear_advice (t : ℕ → ℕ) (ht : Range1 t) :
    ∃ L : Lang,
      (∃ (g : ℕ → ℝ) (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ),
        Filter.Tendsto (fun n : ℕ => g n / n) Filter.atTop (nhds 0) ∧
        ∀ x : List Bool, ContractionLemma.RunsWithin A out x [decide (L x)]
          (C * (2 : ℝ) ^ g x.length) (C * ((x.length : ℝ) + 1) ^ C)) ∧
      ((∀ n, t n = n) → ∃ (A : PrimitiveMachine) (out : Fin A.tapeCount) (C : ℕ),
        ∀ x : List Bool, ContractionLemma.RunsWithin A out x [decide (L x)]
          (C * (2 : ℝ) ^ (C * x.length * Real.logb 2 (Real.logb 2 (x.length + 2) + 2) /
            Real.sqrt (Real.logb 2 (x.length + 2))))
          (C * ((x.length : ℝ) + 1) ^ C)) ∧
      ¬ IOAdvice t (fun n => n) L := by sorry

end ContractionLemma.Supplement
