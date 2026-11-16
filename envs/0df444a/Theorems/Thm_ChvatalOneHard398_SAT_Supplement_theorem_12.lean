-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_Supplement_theorem_12
-- name    : ChvatalOneHard398.SAT.Supplement.theorem_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:30:37.462667+00:00
-- url     : https://prove2.me/theorems/88f54dc3-5abe-4c9c-b507-b3b57649358f
-- title:
--   Theorem 12 — average-case parallelepipeds
-- statement:
--   For every sufficiently large $n$, every prime $q\in[n^3,2n^3]$, and
--   $$k=\lceil\log_2q\rceil,\quad m=3nk,\quad \alpha=\frac1{200n^2k^2\log n},$$
--   let $D$ be the image under Proposition 11's parallelepiped construction of the equal LWE/uniform mixture, with rounded-normal error law $\bar\Psi_\alpha$. This ideal distribution has effective polynomial-time samplers at arbitrary requested numerical precision. Its support consists of parallelepipeds in $\mathbb R^m$ given by integral constraints whose matrix and right-hand-side coefficients have absolute value strictly below $2q$. Moreover,
--   $$\Pr_{Q\sim D}\{Q\text{ is thin}\}\ge1-2^{-2nk}.$$
--   If a uniform randomized polynomial-time algorithm decides integer feasibility with eventual success at least $1/2+n^{-c}$ for some fixed $c>0$, averaging over $D$ and its independent tape, then there is a uniform randomized polynomial-time algorithm solving decision-LWE with these parameters and $m$ samples. Solving means an eventual difference of output-one probabilities of at least $n^{-c'}$ for some fixed $c'>0$.
--
--   This is the average-case parallelepiped companion theorem. No correctness conditional on thinness or per-instance correctness is assumed.
--
--   Differences from the source:
--   - encoding: randomized polynomial-time algorithms → a deterministic polynomial-time TM2 map with a fixed polynomial number of independent fair bits; reason: one finite effective computation is used across every input dimension
--   - encoding: polynomial-time sampling of the ideal rounded-Gaussian pushforward law → sampling to requested event error 2^(-precision), with the same error bound on randomized-test success; reason: finite tapes implement numerical precision while ideal laws and inverse-polynomial advantage are retained
--   - encoding: q=q(n) is any prime in [n³,2n³] and n is sufficiently large → q is supplied explicitly, with an existential fixed eventual threshold and every eventually admissible prime family; reason: this makes uniformity explicit without selecting one prime family or requiring that family to be computable
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.15, Theorem 12. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Supplement_Probability

namespace ChvatalOneHard398.SAT.Supplement
open scoped BigOperators
open CombOpt.ChvatalRank

theorem theorem_12 :
    ∃ N : ℕ, 2 ≤ N ∧
      (∀ n q, N ≤ n → primeRange n q →
        16*(samples n q)^2 < q ∧ 0 < alpha12 n q ∧ alpha12 n q < 1) ∧
      SamplableFrom encPara N paraLaw ∧
      (∀ n q, N ≤ n → primeRange n q →
        (∀ Q ∈ (paraLaw n q).support, Q.d = samples n q ∧ smallCoefficients q Q) ∧
        1-(2 : ℝ)^(-((2*n*bits q : ℕ) : ℤ)) ≤ prob (paraLaw n q) ParaInput.Thin) ∧
      (∀ q : ℕ → ℕ, (∃ Nq : ℕ, ∀ n, Nq ≤ n → primeRange n (q n)) →
        ∀ A : RandomAlg ParaInput Bool, IsPolyRandom encPara encBool A →
          averageAdvantage encPara A paraLaw q ParaInput.Feasible → SolvesLWE alpha12 q) := by sorry

end ChvatalOneHard398.SAT.Supplement
