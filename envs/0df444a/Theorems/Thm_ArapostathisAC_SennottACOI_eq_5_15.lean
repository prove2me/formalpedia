-- Prove2me | Theorems.Thm_ArapostathisAC_SennottACOI_eq_5_15
-- name    : ArapostathisAC.SennottACOI.eq_5_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T15:44:18.955315+00:00
-- url     : https://prove2.me/theorems/a193e5a7-fdb4-4792-9834-04056efb507f
-- title:
--   Display (5.15) — the differential discounted value equation along a discount optimal policy
-- statement:
--   In the countable-state controlled Markov process of §5, let $\beta\in(0,1)$, suppose that $J^*_\beta(i)<\infty$ for every state $i$, and let $f\in\Pi_{SD}$ be $\beta$-discount optimal. Write $h_\beta(i)=J^*_\beta(i)-J^*_\beta(0)$. Then for every state $i$ the series $\sum_j P(j\mid i,f(i))\,h_\beta(j)$ converges and
--   $$(1-\beta)J^*_\beta(0)+h_\beta(i)=c\big(i,f(i)\big)+\beta\sum_{j\in S}P\big(j\mid i,f(i)\big)\,h_\beta(j).$$
--
--   This is display (5.15) in the proof of Theorem 5.9 (the identity (5.6) of p. 301 evaluated at the discount optimal action). It is the relation whose limit as $\beta\uparrow1$ produces the average cost optimality inequality.
--
--   **Formalization Note** The paper writes (5.15) for $\beta=\beta_n$ and $f=f_{\beta_n}$; it is stated here for an arbitrary $\beta\in(0,1)$ and an arbitrary $\beta$-discount optimal $f$, under the finiteness of $J^*_\beta$ (Assumption 5.14 at this $\beta$), which makes $h_\beta$ a genuine difference of real numbers. Convergence of the series is part of the conclusion.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 308, proof of Theorem 5.9, display (5.15); cf. (5.6), p. 301

import Mathlib
import Definitions.Def_ArapostathisAC_SennottACOI_CMP
import Definitions.Def_ArapostathisAC_SennottACOI_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ArapostathisAC.SennottACOI

variable {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]

/-- Display (5.15) (proof of Theorem 5.9, p. 308), the identity (5.6) along a discount optimal
stationary policy: if `β ∈ (0, 1)`, `J*_β` is finite everywhere and `f ∈ Π_SD` is
`β`-discount optimal, then for every state `i` the series `Σ_j P(j | i, f(i)) h_β(j)` converges and
`(1 − β) J*_β(0) + h_β(i) = c(i, f(i)) + β Σ_j P(j | i, f(i)) h_β(j)`. -/
theorem eq_5_15 (M : ArapostathisAC.VanishingDiscount.CMP A) (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (hfin : ∀ i, ArapostathisAC.VanishingDiscount.discValue M β i ≠ ⊤) (f : StationaryPolicy M) (hf : ArapostathisAC.VanishingDiscount.IsDiscOptimal M β f)
    (i : ℕ) :
    Summable (fun j => ArapostathisAC.VanishingDiscount.prob M i (f.1 i) j * ArapostathisAC.VanishingDiscount.hRel M β j) ∧
    (1 - β) * (ArapostathisAC.VanishingDiscount.discValue M β 0).toReal + ArapostathisAC.VanishingDiscount.hRel M β i =
      M.c i (f.1 i) + β * ∑' j, ArapostathisAC.VanishingDiscount.prob M i (f.1 i) j * ArapostathisAC.VanishingDiscount.hRel M β j := by sorry

end ArapostathisAC.SennottACOI
