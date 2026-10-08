-- Prove2me | Theorems.Thm_CompOT_EntropicLimit_eq_4_7
-- name    : CompOT.EntropicLimit.eq_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:26:14.453981+00:00
-- url     : https://prove2.me/theorems/74b83aa6-1dfd-42e0-9b28-d531ef01101e
-- title:
--   (4.7), p. 428 — P_ε is the KL projection of the Gibbs kernel K = e^{−C/ε} onto U(a, b)
-- statement:
--   Let $a$, $b$ be marginals, $C$ a cost matrix, $\varepsilon > 0$, and let $K_{i,j} = e^{-C_{i,j}/\varepsilon}$ be the Gibbs kernel. A matrix $P$ solves the entropic problem (4.2) if and only if it solves the Kullback–Leibler projection problem
--   $$P = \operatorname{Proj}^{\mathrm{KL}}_{U(a,b)}(K) = \operatorname*{argmin}_{P \in U(a,b)} \mathrm{KL}(P\,|\,K).$$
--   In particular the unique solution $P_\varepsilon$ of (4.2) is the KL projection of $K$ onto $U(a,b)$.
--
--   This reformulation is the starting point of Sinkhorn's algorithm.
--
--   **Formalization Note** Stated as an equivalence of the two optimality predicates for every matrix $P$; $\mathrm{KL}$ uses $0\log 0 = 0$.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), (4.6)–(4.7), p. 428

import Mathlib
import Definitions.Def_CompOT_EntropicLimit_Defs

namespace CompOT.EntropicLimit

/-- (4.7), p. 428: for `ε > 0`, a matrix solves (4.2) if and only if it minimizes
`KL(·|K)` over `U(a,b)`, where `K` is the Gibbs kernel `K_{i,j} = exp(-C_{i,j}/ε)`. -/
theorem eq_4_7 {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ) (hε : 0 < ε)
    (P : Matrix (Fin n) (Fin m) ℝ) :
    IsEntropicOptimal C a b ε P ↔
      (P ∈ CompOT.Assignment.couplings a b ∧
        ∀ Q ∈ CompOT.Assignment.couplings a b, klMat P (gibbs C ε) ≤ klMat Q (gibbs C ε)) := by sorry

end CompOT.EntropicLimit
