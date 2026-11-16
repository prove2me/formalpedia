-- Prove2me | Theorems.Thm_ContractionLemma_Supplement_theorem_13_separations
-- name    : ContractionLemma.Supplement.theorem_13_separations
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:29:01.101002+00:00
-- url     : https://prove2.me/theorems/189a9a86-387f-4588-b008-10dda5820fe0
-- title:
--   Theorem 13, p.40 — separations of $\mathsf E$ from $\bigcup\mathcal C_t$ and $\mathsf{QMATIME}[t,w]$, and of $\mathsf{NE}$ from $\mathsf{MATIME}$, $\Sigma_2\mathsf{TIME}$, $\mathsf{QCMATIME}$
-- statement:
--   Let $t$ be time-constructible with $n\le t(n)=o(n\sqrt{\log n})$ (the range (1)), and fix a gate set. Then:
--
--   1. **(a)** $\mathsf E$ is not contained in any class of $\mathcal C_t$, and indeed not in their union: some language in $\mathsf E$ lies in none of $\mathsf{BPTIME}[t]$, $\mathsf{NTIME}[t]$, $\mathsf{coNTIME}[t]$, $\mathsf{PPTIME}[t]$, $\oplus\mathsf{TIME}[t]$, $\mathsf{PostBPTIME}[t]$, $\mathsf{BQTIME}[t]$, $\mathsf{PostBQTIME}[t]$. In particular, $\mathsf E$ is not contained in randomized, nondeterministic, counting, parity, or quantum linear time, even with postselection.
--   2. **(b)** $\mathsf E\not\subseteq\mathsf{QMATIME}[t,w]$ for every witness length $w=o(n)$.
--   3. **(c)** $\mathsf{NE}\not\subseteq\mathsf{MATIME}[t]\cup\Sigma_2\mathsf{TIME}[t]\cup\mathsf{QCMATIME}[t]$.
--
--   Simulation by exhaustive search does not give (a), because a single language in $\mathsf E$ must defeat every constant in the running time $c\,t(n)$ at once.
--
--   Differences from the source:
--   - encoding: $w=o(n)$; the range (1) → $w(n)/n\to0$; $t$ time-constructible, $n\le t(n)$ and $t(n)/(n\sqrt{\log_2(n+2)})\to0$; reason: explicit limits for the $o(\cdot)$ conditions
--   - encoding: E, NE "for multitape machines" → $\bigcup_c\mathsf{DTIME}[2^{cn}]$ and $\bigcup_c\mathsf{NTIME}[2^{cn}]$ with local machines; reason: local machines with fixed parameters and multitape machines simulate each other with constant overhead, so the classes are equal
--   - encoding: time $O(t)$ (clocks $c\,t(n)$, at most $c\,t(n)$ gates, ancillas and witness bits; time-constructibility within $O(t(n))$ steps) → $c\,(t(n)+1)$; reason: equal to $c\,t(n)$ up to the constant for $n\ge1$, since $t(n)\ge n\ge1$; at $n=0$ it avoids the junk bound $0$, under which no machine halts and $t(n)=n$ would not be time-constructible
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Theorem 13, p.40 (stated first on p.9); range (1), p.9; Definitions 2.7–2.9, pp.20–21

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

/-- **Theorem 13 (Separations)** — Gajulapalli, *The Contraction Lemma Beyond ETH* (manuscript,
sha256 049caea1…), p.40 (PDF p.43; stated first on p.9).

"For every time-constructible `t` in the range (1):
(a) E is not contained in any class of `C_t`, and indeed not in their union. In particular, E is not
contained in randomized, nondeterministic, counting, parity, or quantum linear time, even with
postselection.
(b) `E ⊄ QMATIME[t, w]` for every witness length `w = o(n)`.
(c) `NE ⊄ MATIME[t] ∪ Σ₂TIME[t] ∪ QCMATIME[t]`."

For every `t` in the range (1) (time-constructible, `n ≤ t(n) = o(n√log n)`) and every gate set `G`:
(a) some language in E is in none of the eight classes of `C_t`; (b) for every `w` with
`w(n)/n → 0`, some language in E is not in `QMATIME[t, w]`; (c) some language in NE is in none of
`MATIME[t]`, `Σ₂TIME[t]`, `QCMATIME[t]`.

**Formalization Note.** "Not in any class, and indeed not in their union" is the union form; the
"in particular" sentence is the case `t(n) = n`, which lies in the range (1). The quantum classes are
over the fixed gate set `G` (p.21). -/
theorem theorem_13_separations (t : ℕ → ℕ) (ht : Range1 t) (G : GateSet) :
    (∃ L : Lang, InE L ∧ ¬ InCt G t L) ∧
    (∀ w : ℕ → ℕ, Filter.Tendsto (fun n : ℕ => (w n : ℝ) / n) Filter.atTop (nhds 0) →
      ∃ L : Lang, InE L ∧ ¬ QMATIME G t w L) ∧
    (∃ L : Lang, InNE L ∧ ¬ (MATIME t L ∨ Sigma2TIME t L ∨ QCMATIME G t L)) := by sorry

end ContractionLemma.Supplement
