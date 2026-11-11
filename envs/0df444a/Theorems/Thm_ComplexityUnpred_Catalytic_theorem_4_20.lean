-- Prove2me | Theorems.Thm_ComplexityUnpred_Catalytic_theorem_4_20
-- name    : ComplexityUnpred.Catalytic.theorem_4_20
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:03:47.761561+00:00
-- url     : https://prove2.me/theorems/97ee09e0-8bc9-4b73-a401-b39c766cec0d
-- title:
--   Theorem 4.20 — FastCatTape(M, p_M) reduces to UNPRED for every catalytic logspace machine M
-- statement:
--   For every catalytic logspace machine $M$ (with catalytic space $p(n)$) there is a logspace-computable polynomially bounded function $p_M:\mathbb N\to\mathbb N$ such that
--   $$\textsf{FastCatTape}(M,p_M)\le_P\textsf{UNPRED}:$$
--   deterministic polynomial-time maps $f,g$ such that for every input $x$, $f(x)$ is a valid UNPRED instance and, for **every** UNPRED solution $S$ of $f(x)$, $g(x,S)$ is a catalytic tape $\tau\in\{0,1\}^{p(|x|)}$ with $\mathrm{time}(M(x,\tau))\le p_M(|x|)$.
--
--   It is the composition of Theorems 4.19, 4.18 and 4.8, and the heart of Theorem 1.5.
--
--   **Formalization Note** FastCatTape is the search problem of Definition 4.1 on the published catalytic machine; every input is valid.
--
--   Differences from the source:
--   - generalization: catalytic logspace machine: catalytic space d n^d, work d log n (Definitions 2.6, 2.8, 2.10) → IsCatalyticLogspace M C p: the published binary machine, any polynomial p ∈ ℕ[X] of catalytic length, any C ≥ 1, work ≤ C(⌊log₂(|x|+2)⌋+1) visited cells; reason: contains the paper's machines (p := d X^d, C := d up to the constant-factor cost of a binary work alphabet), so the statement specializes to them
--   - reading: logspace-computable function (model not fixed) → LogspaceComputable / LogspaceComputableNat: the published machine with an empty catalytic tape, binary output (least significant bit first), O(log) visited work cells; for ℕ → ℕ, computed from any input of length N; reason: the ordinary logspace transducer; binary and unary output are interchangeable for polynomially bounded values
--   - encoding: polynomially bounded: f(N) ≤ poly(N) → f N ≤ N^k + k for some k; reason: every polynomial is bounded by N^k + k for some k
--   - encoding: ≤P: both maps computable in deterministic polynomial time → CardinalMatching.SearchReduces with CookPvsNP.PolyTimeComputable (one-tape Cook machines, time |x|^k + k); the solution map reads the tagged pair (x, y); reason: the published platform reduction; it requires correctness for every answer, as §2.2 does
--   - encoding: UNPRED instances (n, r in unary, circuits, indices) and multiset answers, no code fixed → the codes UnpredInstance.encode and encStrings of the UNPRED definition; reason: one concrete prefix-free binary code, polynomially equivalent to any reasonable one
--   - reading: THRESHOLD gates with unspecified thresholds → gates Th_t (at least t inputs are 1), t in the gate label; reason: the paper does not fix the thresholds; Th_t is the standard reading and keeps the gate in the basis
-- source:
--   Agarwala, Dorfman, The Complexity of Unpredictability, arXiv:2611.05956v1, p. 39, Theorem 4.20

import Mathlib
import Definitions.Def_CardinalMatching_SearchReduces
import Definitions.Def_ComplexityUnpred_Catalytic_UNPRED
import Definitions.Def_ComplexityUnpred_Catalytic_FastCatTape

namespace ComplexityUnpred.Catalytic

open CatalyticMatching.General

/-- **Theorem 4.20** (Agarwala, Dorfman, arXiv:2611.05956v1, p. 39). For every catalytic
logspace machine `M` (catalytic space `p(n)`) there is a logspace-computable polynomially
bounded `p_M : ℕ → ℕ` with `FastCatTape(M, p_M) ≤_P UNPRED`. -/
theorem theorem_4_20 (M : Machine) (Cw : ℕ) (p : Polynomial ℕ)
    (hM : IsCatalyticLogspace M Cw p) :
    ∃ pM : ℕ → ℕ, LogspaceComputableNat pM ∧ PolyBounded pM ∧
      CardinalMatching.SearchReduces (FastCatTape M p pM) UNPRED := by sorry

end ComplexityUnpred.Catalytic
