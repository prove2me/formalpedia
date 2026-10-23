-- Prove2me | Theorems.Thm_AssemblyCoord_Feedback_prop_2_step1_min_profit
-- name    : AssemblyCoord.Feedback.prop_2_step1_min_profit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:35.037283+00:00
-- url     : https://prove2.me/theorems/db68a0a4-0b96-4a58-8dea-2c10f9d09d06
-- title:
--   Proof of Proposition 2, Step 1, oa6 (PDF 38) — the all-minimum path attains the minimum profit (25) in every subgame along it
-- statement:
--   In the $M$-contractor, $N$-period coordination game with information feedback started from zero effort, under the standing assumptions, let $\sigma$ be any strategy profile along whose path every contractor exerts $\underline q/N$ in every period. Let $h_n$ be the history of the first $n$ periods of that path, $0 \le n < N$. Then for every subgame-perfect equilibrium $\sigma'$ and every contractor $i$,
--   $$\pi_i\big(\hat{\mathbf q}_N(\sigma \mid h_n)\big) \le \pi_i\big(\hat{\mathbf q}_N(\sigma' \mid h_n)\big),$$
--   where $\hat{\mathbf q}_N(\tau \mid h)$ denotes the final effort levels when $\tau$ is played from history $h$ to the end of period $N$.
--
--   In words: continuing the all-minimum path gives every contractor the lowest profit among all SPE continuations of the subgame, which is condition (25) of the paper for this path. It is the step from "SPE" to "SPSE" in the existence half of Proposition 2(i).
--
--   **Formalization Note.** Neither $N \le M - 1$ nor that $\sigma$ is an SPE is needed, and neither is assumed. Periods are 0-based (`pathHist σ n`).
-- source:
--   Zhang, Shokoohyar, Qi & Katok, Coordination for assembly, author manuscript (10 July 2025) of MSOM doi:10.1287/msom.2023.0342, p. oa6 (PDF 38), proof of Proposition 2, Step 1, (25)

import Mathlib
import Definitions.Def_AssemblyCoord_Feedback_Model

namespace AssemblyCoord.Feedback

theorem prop_2_step1_min_profit (P : Params) (hP : P.Standing) (σ : Profile P.M)
    (hpath : ∀ n, n < P.N → ∀ i : Fin P.M, σ i (pathHist σ n) = P.qlo / P.N) :
    ∀ n, n < P.N → ∀ σ' : Profile P.M, P.IsSPE 0 σ' → ∀ i : Fin P.M,
      P.profit (P.final 0 σ (pathHist σ n)) i ≤ P.profit (P.final 0 σ' (pathHist σ n)) i := by sorry

end AssemblyCoord.Feedback
