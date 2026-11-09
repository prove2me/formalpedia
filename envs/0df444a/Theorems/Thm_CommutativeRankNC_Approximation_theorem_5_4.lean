-- Prove2me | Theorems.Thm_CommutativeRankNC_Approximation_theorem_5_4
-- name    : CommutativeRankNC.Approximation.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:54:24.701939+00:00
-- url     : https://prove2.me/theorems/a8756026-a2ae-4895-a842-740df1fac1b1
-- title:
--   Theorem 5.4 — Uniform logarithmic boosting schedule
-- statement:
--   For each fixed integer $k\ge1$, the sign-start, first-maximum boosting sequence has a predetermined schedule $T_k(n)=O_k(\log(n+1))$, independent of the optimum and the matrix entries. Its contraction constant satisfies $0<\rho_k<1$ and $\rho_k^{T_k(n)}kn<1$. For every rational input tuple the scheduled output obeys
--
--   $$A_{T_k(n)}\in\mathcal B,\qquad\operatorname{rank}A_{T_k(n)}\ge\frac{k}{k+1}\operatorname{crk}(\mathcal B).$$
--
--   Ranks never decrease. One common constant depending only on $k$ bounds the schedule and, when each input numerator and denominator has at most $L$ bits, the output-entry bit length by $C_k(mL+mT_k(n)+\ell(mn))$, where $\ell(u)=\lfloor\log_2(u+2)\rfloor+1$. These are the source's logarithmic schedule and page-24 rational bit accounting.
--
--   Differences from the source:
--   - generalization: the positive-dimensional matrix setting → also zero-dimensional matrices and empty generating lists; reason: the zero matrix and empty blocks supply these extra cases without excluding any source instance
--   - encoding: one-based matrix and variable indices → zero-based finite index types and ordered pairs for truncated blocks; reason: the same entries and blocks are present under a bijective reindexing
--   - encoding: T chosen so ρₖᵀkn<1 and T=Oₖ(log n) → Tₖ(n)=2·50ᵏ·(floor(log₂(kn+1))+1), with uniform all-n bounds and integer-log offsets; reason: ρₖ≤1−50⁻ᵏ gives the displayed sufficient schedule; the offsets handle n=0 and n=1 without altering the asymptotic claim
--   - encoding: page-24 bit lengths and rank-maximizing sequence → maximum numerator/denominator binary length, and finite-minor rank tests with first-maximum tie breaking; reason: these determine the actual scalar sequence without assigning unit Boolean cost to a rank oracle; the sign bit and logarithmic offsets are absorbed into Cₖ
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), Theorem 5.4, PDF/printed p.23; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Definitions.Def_CommutativeRankNC_Approximation_ConstructionCodes

namespace CommutativeRankNC.Approximation

/-- Theorem 5.4, PDF/printed p.23, with the fixed schedule, rank monotonicity
and bit accounting on p.24 made explicit. Constants depend only on fixed k. -/
theorem theorem_5_4 (k : ℕ) (hk : 0 < k) :
    0 < rho k ∧ rho k < 1 ∧ ∃ C : ℕ, 0 < C ∧ ∀ n : ℕ,
      roundSchedule k n ≤ C * logBound n ∧
      rho k ^ roundSchedule k n * (k : ℝ) * (n : ℝ) < 1 ∧
      ∀ (m : ℕ) (B : Fin m → QMatrix n),
        (iterateMatrix k B (roundSchedule k n)) ∈ matrixSpace B ∧
        (k : ℝ) / ((k : ℝ)+1) * (commutativeRank B : ℝ) ≤
          ((iterateMatrix k B (roundSchedule k n)).rank : ℝ) ∧
        (∀ j, (iterateMatrix k B j).rank ≤ (iterateMatrix k B (j+1)).rank) ∧
        ∀ L : ℕ, (∀ i u v, rationalBitSize (B i u v) ≤ L) →
          ∀ u v, rationalBitSize (iterateMatrix k B (roundSchedule k n) u v) ≤
            C * (m*L + m*roundSchedule k n + logBound (m*n)) := by sorry

end CommutativeRankNC.Approximation
