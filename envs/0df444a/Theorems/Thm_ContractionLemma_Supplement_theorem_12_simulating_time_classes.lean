-- Prove2me | Theorems.Thm_ContractionLemma_Supplement_theorem_12_simulating_time_classes
-- name    : ContractionLemma.Supplement.theorem_12_simulating_time_classes
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:28:27.706867+00:00
-- url     : https://prove2.me/theorems/896955fa-33ef-4e50-a482-1b63fe331142
-- title:
--   Theorem 12, p.40 — $\bigcup_{\mathcal C\in\mathcal C_t}\mathcal C\subseteq\mathsf{DTIME}[2^{O(t/\sqrt{\log t})}]$
-- statement:
--   For every time-constructible $t(n)\ge n$ and every fixed gate set,
--
--   $$
--   \bigcup_{\mathcal C\in\mathcal C_t}\mathcal C\;\subseteq\;\mathsf{DTIME}\bigl[2^{O(t/\sqrt{\log t})}\bigr],
--   $$
--
--   where $\mathcal C_t=\{\mathsf{BPTIME}[t],\mathsf{NTIME}[t],\mathsf{coNTIME}[t],\mathsf{PPTIME}[t],\oplus\mathsf{TIME}[t],\mathsf{PostBPTIME}[t],\mathsf{BQTIME}[t],\mathsf{PostBQTIME}[t]\}$. That is, every language in one of these eight classes is decided by a deterministic machine in time $c\,\lceil2^{c\,t(n)/\sqrt{\log_2(t(n)+2)}}\rceil$ for some constant $c$.
--
--   The right-hand side is $2^{o(n)}$ exactly in the range $n\le t(n)=o(n\sqrt{\log n})$, which gives the separations of Theorem 13.
--
--   Differences from the source:
--   - encoding: $\mathsf{DTIME}[2^{O(t/\sqrt{\log t})}]$ and the classes of $\mathcal C_t$ → $\bigcup_c\mathsf{DTIME}[\lceil2^{c f(t(n))}\rceil]$, all classes with the local machines and uniform circuit families of §2.5–2.6; reason: Lean model of Definitions 2.8–2.9; $f(u)=u/\sqrt{\log_2(u+2)}$
--   - encoding: time $O(t)$ (clocks $c\,t(n)$, at most $c\,t(n)$ gates, ancillas and witness bits; time-constructibility within $O(t(n))$ steps) → $c\,(t(n)+1)$; reason: equal to $c\,t(n)$ up to the constant for $n\ge1$, since $t(n)\ge n\ge1$; at $n=0$ it avoids the junk bound $0$, under which no machine halts and $t(n)=n$ would not be time-constructible
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), Theorem 12, p.40 (stated first on p.9); Definitions 2.8, 2.9, pp.20–21

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

/-- **Theorem 12 (Simulating time classes)** — Gajulapalli, *The Contraction Lemma Beyond ETH*
(manuscript, sha256 049caea1…), p.40 (PDF p.43; stated first on p.9).

"For every time-constructible `t(n) ≥ n`, `⋃_{C∈C_t} C ⊆ DTIME[2^{O(t/√log t)}]`."

For every time-constructible `t` with `t(n) ≥ n` and every gate set `G`, every language in one of
the eight classes `BPTIME[t]`, `NTIME[t]`, `coNTIME[t]`, `PPTIME[t]`, `⊕TIME[t]`, `PostBPTIME[t]`,
`BQTIME[t]`, `PostBQTIME[t]` (the quantum ones over `G`) lies in `DTIME[2^{c f(t(n))}]` for some
`c`, `f(u) = u/√log₂(u+2)`.

**Formalization Note.** The classes are defined with the local machines and uniform circuit families
of §2.5–2.6 (Definitions 2.8, 2.9); "all statements below hold for every fixed `G`" (p.21). -/
theorem theorem_12_simulating_time_classes (t : ℕ → ℕ) (ht : TimeConstructible t)
    (hn : ∀ n, n ≤ t n) (G : GateSet) (L : Lang) (hL : InCt G t L) : InDTIMEexpF t L := by sorry

end ContractionLemma.Supplement
