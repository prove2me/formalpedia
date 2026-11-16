-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_Supplement_theorem_29
-- name    : ChvatalOneHard398.SAT.Supplement.theorem_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:31:49.337385+00:00
-- url     : https://prove2.me/theorems/3a3ac512-8ed8-4f6d-8e22-a13dcea3ddc5
-- title:
--   Theorem 29 — average-case thin formulas
-- statement:
--   For every sufficiently large $n$ and every prime $q\in[n^3,2n^3]$, put
--   $$k=\lceil\log_2q\rceil,\quad m=3nk,\quad \alpha=\frac1{200n^{3/2}k^{5/2}\log n}.$$
--   Let $h$ be the largest integer with $h2^h\le q/(4m^{3/2})$, and take one maximal prime power at most $h$ for each prime at most $h$. For each residue pair $(A,t)$, use the kernel matrix of Lemma 28 and the published formula $F(p,h,H,q,t)$. Let $\mathcal F$ be its distribution under the equal LWE/uniform mixture with error law $\bar\Psi_\alpha$.
--
--   The ideal law has effective polynomial-time samplers to arbitrary numerical precision. Its support consists of well-formed formulas with at most three literals per clause, with
--   $$N\le10000n^2k^4\le6250000n^2(\log_2n)^4.$$
--   The generated parameters are valid and their formulas are thin with probability at least $1-2^{-2nk}$. If a uniform randomized polynomial-time algorithm decides satisfiability with eventual success at least $1/2+n^{-c}$ for some fixed $c>0$ under this unconditioned law and its independent tape, then a uniform randomized polynomial-time algorithm solves decision-LWE with the displayed parameters and $m$ samples, with eventual inverse-polynomial distinguishing advantage.
--
--   This is the SAT average-case companion to the worst-case mission goal. It uses the existing formula and its full asymmetric box without changing its target shift.
--
--   Differences from the source:
--   - encoding: randomized polynomial-time algorithms → a deterministic polynomial-time TM2 map with a fixed polynomial number of independent fair bits; reason: one finite effective computation is used across every input dimension
--   - encoding: polynomial-time sampling of the ideal rounded-Gaussian pushforward law → sampling to requested event error 2^(-precision), with the same error bound on randomized-test success; reason: finite tapes implement numerical precision while ideal laws and inverse-polynomial advantage are retained
--   - encoding: q=q(n) is any prime in [n³,2n³] and n is sufficiently large → q is supplied explicitly, with an existential fixed eventual threshold and every eventually admissible prime family; reason: this makes uniformity explicit without selecting one prime family or requiring that family to be computable
--   - encoding: maximal prime powers at most h and the formula of Proposition 16 → increasing prime order, canonical elimination H and the unchanged published latticeFormula; reason: this fixes representation choices without changing error boxes or target shifts
--   - encoding: O(n² log⁴ n) variables → N≤10000 n² k⁴ and N≤6250000 n²(log₂ n)⁴ eventually; reason: the explicit universal constants follow from the published formulaBound and the estimates on p.30, as derived in SUPPLEMENT.md
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.30, Theorem 29. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Supplement_Probability

namespace ChvatalOneHard398.SAT.Supplement
open scoped BigOperators
open CombOpt.ChvatalRank

theorem theorem_29 :
    ∃ N : ℕ, 2 ≤ N ∧
      (∀ n q, N ≤ n → primeRange n q →
        7 ≤ height n q ∧ 0 < alpha29 n q ∧ alpha29 n q < 1) ∧
      SamplableFrom encFormula N formulaLaw ∧
      (∀ n q, N ≤ n → primeRange n q →
        (∀ F ∈ (formulaLaw n q).support,
          F.WellFormed ∧ (∀ T ∈ F.clauses, T.card ≤ 3) ∧
          F.N ≤ 10000*n^2*(bits q)^4 ∧
          (F.N : ℝ) ≤ 6250000*(n : ℝ)^2*(Real.log n/Real.log 2)^4) ∧
        (1-(2 : ℝ)^(-((2*n*bits q : ℕ) : ℤ)) ≤
          prob (mixtureLaw n (samples n q) q (roundedGaussian (alpha29 n q) q))
            (fun a => (formulaParams a).Valid ∧ IsThin (formulaParams a)))) ∧
      (∀ q : ℕ → ℕ, (∃ Nq : ℕ, ∀ n, Nq ≤ n → primeRange n (q n)) →
        ∀ A : RandomAlg Formula Bool, IsPolyRandom encFormula encBool A →
          averageAdvantage encFormula A formulaLaw q Satisfiable → SolvesLWE alpha29 q) := by sorry

end ChvatalOneHard398.SAT.Supplement
