-- Prove2me | Theorems.Thm_FasterDistributedMatching_ApproximateMatching_fmu_local_booster
-- name    : FasterDistributedMatching.ApproximateMatching.fmu_local_booster
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T22:38:25.716903+00:00
-- url     : https://prove2.me/theorems/b676b818-fcfb-4610-a6ee-001b080e4bc1
-- title:
--   Polynomial-accuracy LOCAL matching booster with physical round accounting
-- statement:
--   Fix a constant approximation fraction $c\in(0,1]$. There are positive integers $p,C$, depending only on $c$, that implement the Fischer--Mitrović--Uitto matching booster in the synchronous deterministic LOCAL model.
--
--   Fix a polynomial identifier convention $b$ and a protocol $A$ that, on every bounded finite simple graph with identifiers below $\max\{2,n\}^{b+4}$, reports an actual matching of size at least $c$ times the optimum. Then there is one protocol $B$, fixed before network inputs and the integer accuracy parameter $q$, that for every $q\ge2$ reports a matching $M$ satisfying
--
--   $$
--   \operatorname{OPT}(G)\le(1+1/q)|M|.
--   $$
--
--   Write $T_A(n,\Delta)$ for the round count of $A$ with common bounds $(n,\Delta)$. Protocol $B$ satisfies
--
--   $$
--   T_B(n,\Delta,q)\le C(q+1)^p\left(T_A\big((n+1)(q+1)^p,(\Delta+1)(q+1)^p\big)+(q+1)^p\right).
--   $$
--
--   The input to $B$ consists of the common bounds and $q$, the processor's own identifier, and its neighbor identifiers; its identifiers need only be below $\max\{2,n\}^{b+1}$. All simulated communication is charged in physical rounds, and all private tapes are ignored. This separates the booster from the construction and time analysis of a constant-approximation oracle.
--
--   **Formalization Note** This is the LOCAL specialization of the framework, with reciprocal integer accuracy, one polynomial padding large enough for all auxiliary graph sizes, degrees, routes and processing times, and a common padded bound used for every oracle invocation. Specializing the source parameter to $1/(2q)$ gives the stated approximation factor.
-- source:
--   Fischer--Mitrović--Uitto, Deterministic (1+epsilon)-Approximate Maximum Matching with poly(1/epsilon) Passes in the Semi-Streaming Model and Beyond, https://arxiv.org/pdf/2106.04179, Theorem 1.2 (PDF p.3), Theorem 6.1 and Sections 6.1--6.7 (PDF pp.26--32), including the bounded-loop remark after Theorem 6.1. LOCAL specialization used by Ghaffari--Grunau submission #1024, Section 3.5, printed p.15 / PDF p.17.

import Mathlib
import Definitions.Def_FasterDistributedMatching_ApproximateMatching_Local
open FasterDistributedMatching.ApproximateMatching

theorem FasterDistributedMatching.ApproximateMatching.fmu_local_booster :
    ∀ c : ℝ, 0 < c → c ≤ 1 →
      ∃ p C : ℕ, 1 ≤ p ∧ 0 < C ∧
        ∀ (b : ℕ) (A : Deterministic Bounds (Finset ℕ) (Option ℕ)),
          (∀ (N : ℕ) (G : SimpleGraph (Fin N)) (k : Bounds),
            boundedGraph G k.n k.degree →
            ∀ ids : Fin N → ℕ, Identifiers k.n (b+4) ids →
              ∃ M : SimpleGraph (Fin N),
                ReportsMatching G ids (execute A G k ids (neighborIDs G ids)) M ∧
                c*(optimum G:ℝ) ≤ (matchingSize M:ℝ)) →
          ∃ B : Deterministic (Bounds × ℕ) (Finset ℕ) (Option ℕ),
            (∀ (k : Bounds) (q : ℕ), 2 ≤ q →
              B.program.rounds (k,q) ≤ C*(q+1)^p*
                (A.program.rounds ⟨(k.n+1)*(q+1)^p,(k.degree+1)*(q+1)^p⟩+(q+1)^p)) ∧
            ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (k : Bounds) (q : ℕ),
              2 ≤ q → boundedGraph G k.n k.degree →
              ∀ ids : Fin N → ℕ, Identifiers k.n (b+1) ids →
                ∃ M : SimpleGraph (Fin N),
                  ReportsMatching G ids (execute B G (k,q) ids (neighborIDs G ids)) M ∧
                  (optimum G:ℝ) ≤ (1+1/(q:ℝ))*(matchingSize M:ℝ) := by sorry
