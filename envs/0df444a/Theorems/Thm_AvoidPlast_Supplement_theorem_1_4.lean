-- Prove2me | Theorems.Thm_AvoidPlast_Supplement_theorem_1_4
-- name    : AvoidPlast.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:41:46.037136+00:00
-- url     : https://prove2.me/theorems/c6d28571-3c00-4aa1-bbc9-021b8a9eb5b6
-- title:
--   Theorem 1.4 — worst-case plasticity for exponential time
-- statement:
--   Under the assumptions of Theorem 1.2, that is $\mathrm{prBP}^*\mathrm L=\mathrm{prL}$ and Assumption 1.1 with $p(n)=n^{-\omega(1)}$,
--   $$\mathsf E\subseteq\bigcap_{\varepsilon>0}\mathrm{DSPACE}[2^{\varepsilon n}];$$
--   and under the assumptions of Theorem 1.3, that is $\mathrm{DSPACE}[O(n)]\not\subseteq\mathrm{i.o.SIZE}^{\mathrm{SAT}}[2^{\delta n}]$ for some $\delta>0$ and Assumption 1.1 with $p(n)=n^{-\omega(1)}$ for a family evaluable in simultaneous time $\mathrm{poly}(n)$ and space $n^{\varepsilon^2}$,
--   $$\mathsf E\subseteq\bigcap_{\varepsilon>0}\bigcup_{k}\Sigma_k\mathrm{TIME}[2^{\varepsilon n}].$$
--
--   The average-case simulations of Theorems 5.8 and 5.9 become worst-case simulations for exponential time, through the worst-case to average-case reductions of Theorems 5.10 and 5.11.
--
--   Differences from the source:
--   - encoding: $\mathrm{DSPACE}[2^{\varepsilon n}]$ → $O(\cdot)$ with an explicit existential constant, $C\cdot(s(n)+1)$; reason: the mission's reading R2; the $+1$ covers $n=0$
--   - encoding: $\Sigma_k\mathrm{TIME}[2^{\varepsilon n}]$ → time $O(\lceil2^{\varepsilon n}\rceil)$; reason: time bounds are natural numbers
--   - reading: Assumption 1.1 with $p(n)=n^{-\omega(1)}$ → a negligible $p:\mathbb N\to(0,1)$ chosen together with the family for each $\varepsilon$ (the base `Assumption11`, and `Assumption11TS` for the time-and-space version); reason: the base mission's reading R1 of Theorem 5.14 item 2
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 1.4, p.4 (PDF p.6)

import Mathlib
import Definitions.Def_AvoidPlast_Assumption11
import Definitions.Def_AvoidPlast_PrBPstarLEqPrL
import Definitions.Def_AvoidPlast_Supplement_InE
import Definitions.Def_AvoidPlast_Supplement_InSPACE
import Definitions.Def_AvoidPlast_Supplement_InSigmaTIME
import Definitions.Def_AvoidPlast_Supplement_SATLowerBound
import Definitions.Def_AvoidPlast_Supplement_Assumption11TS

namespace AvoidPlast.Supplement

open AvoidPlast

/-- Theorem 1.4, worst-case plasticity for exponential time (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.4). Under the assumptions
of Theorem 1.2 (`prBP*L = prL` and Assumption 1.1 with `p(n) = n^{-ω(1)}`),
`E ⊆ ∩_{ε>0} DSPACE[2^{εn}]`; and under the assumptions of Theorem 1.3
(`DSPACE[O(n)] ⊄ i.o.SIZE^SAT[2^{δn}]` for some `δ > 0`, and Assumption 1.1 with `p(n) = n^{-ω(1)}`
for a family evaluable in simultaneous time `poly(n)` and space `n^{ε²}`),
`E ⊆ ∩_{ε>0} ∪_k Σ_kTIME[2^{εn}]`.

**Formalization Note** `DSPACE[2^{εn}]` is space `O(2^{εn})` (reading R2) and `Σ_kTIME[2^{εn}]` is
time `O(⌈2^{εn}⌉)`. -/
theorem theorem_1_4 :
    (PrBPstarLEqPrL → Assumption11 →
      ∀ L : Set (List Bool), InE L → ∀ ε : ℝ, 0 < ε → InSPACE (fun n => (2 : ℝ) ^ (ε * n)) L) ∧
    (SATLowerBound → Assumption11TS →
      ∀ L : Set (List Bool), InE L → ∀ ε : ℝ, 0 < ε →
        ∃ k : ℕ, InSigmaTIME k (fun n => ⌈(2 : ℝ) ^ (ε * n)⌉₊) L) := by sorry

end AvoidPlast.Supplement
