-- Prove2me | Theorems.Thm_AggregatedCodeTesting_Testing_Supplement_theorem_11
-- name    : AggregatedCodeTesting.Testing.Supplement.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T11:30:46.677671+00:00
-- url     : https://prove2.me/theorems/8cfdc8fa-52d9-4d06-ac1e-b6293d511123
-- title:
--   Theorem 11 — minimax exact profile recovery, moment decoder and bit complexity
-- statement:
--   Fix $C\le\mathbb F_2^m$ without identically zero coordinates and $S=s^*(C)>0$. Then $S$ is finite. There are positive constants $K_C,c_C$ and a threshold $w_0(C)\ge1$ such that for every $w\ge1$ and $0<\eta\le1/8$, the single moment decoder defined above recovers the entire unknown block-coset profile, uniformly over all offset sequences, using
--
--   $$N\le K_Cw^S\log(1/\eta),\qquad
--   \sup_\ell\Pr_\ell\{\widehat T\ne T_C(\ell)\}\le\eta.$$
--
--   In detail, $N=nR$, $n=128\operatorname{Bell}(2S)w^S$, and one can choose a positive odd integer $R\ge4\log(2B_C/\eta)$, where $B_C$ is the number of retained nonconstant blockwise moments. The decoder takes coordinatewise medians of the disjoint batch means, rounds them to integers, takes exact rational formal-logarithm coefficients, divides by the precomputed nonzero witness coefficients and Walsh-inverts as in (15). It checks nonnegative integral counts of total width $w$ and otherwise returns the fixed zero-offset profile. On every observation list its output is a valid profile. It accesses observations only through these moments of degree at most $S$, and never enumerates candidate profiles. No density condition is imposed.
--
--   For every $w\ge w_0(C)$, every $0<\eta\le1/8$, every integer sample size $N$ and every estimator, with arbitrary internal randomness, worst-case error at most $\eta$ implies
--
--   $$N\ge c_Cw^S\log(1/\eta).$$
--
--   This includes estimators that can return invalid outputs; those outputs count as errors. The target is the block-coset histogram, not cross-block lane alignment.
--
--   The theorem also supplies one universal deterministic bit-machine preprocessor with universal positive polynomial coefficient $a$ and natural degree $d$, before any code is quantified. It produces the exact selected witness table for every informative indecomposable block within the Appendix B polynomial bound in $m_D,q_D,D_0,M_D$, and produces the full code's stored table within
--
--   $$P(C)=a\left(1+m+\sum_{D\text{ informative}}(m_D+q_D+D_0+M_D)\right)^d,$$
--
--   where $q_D=|C_D^\perp|$, $D_0=(\max_{A\in C_D^\perp}|A|)q_D/2$ and $M_D=\binom{m_D+D_0}{m_D}$. For this fixed code there is one online program, independent of $w,\eta,R$ and the unknown profile, whose actual execution on every observation list and every random tape returns the specified decoder in at most $Na_C(1+L)^{d_C}$ steps. Here $L=\lceil\log_2(w+1)\rceil+\lceil\log_2(N+1)\rceil$ and $a_C>0,d_C$ depend only on $C$. The composed cost is
--
--   $$P(C)+N\operatorname{poly}_C(\log(w+1)+\log(N+1)).$$
--
--   Thus the theorem retains both the statistical minimax guarantee and the constructive/computational clauses. The witness-table bound includes $M_D$; it is not asserted polynomial solely in $m$ and $2^r$.
--
--   Differences from the source:
--   - encoding: profile estimators with optional internal randomness → PMF kernels on all profile-shaped outputs, with exact product-law error; reason: this includes every deterministic and randomized estimator, and counts invalid outputs as failures
--   - encoding: choose a leading monomial, estimate and round moments, and invert (15) → degree-first binary monomial selection, exact rational batch medians, nearest-integer rounding, formalLog coefficients and arithmetic validity checks; reason: these fix deterministic choices permitted by the proof without enumerating candidate profiles
--   - encoding: schoolbook bit operations after code-only preprocessing → actual transitions of the published multi-tape binary Turing machine with explicit binary inputs and stored witness tables; reason: standard bit computation supports schoolbook arithmetic in polynomial time; separate preprocessing and online execution bounds add to the stated total
--   - encoding: polynomial preprocessing bound per informative block and code-only online polynomial → universal polynomial majorants with aggregate size m plus the sum of block parameters and binary ceiling logarithms online; reason: a polynomial majorant absorbs matrix reading, block identification, concatenation and logarithm-base constants; M_D is retained
--   - encoding: finite positive S and all positive widths and confidence levels → finiteness is a conclusion, w is a positive natural, and a suitable positive odd batch count is chosen for each real eta; reason: the single decoder program reads the batch parameters and never needs an exact real eta as machine input
-- source:
--   Jianxin Wang, Zixuan Wang, Chenxu Pang, Chaoen Xiao, Lei Zhang, Zaitian Fu, Conghui Zheng, Yiyang Zou, STOC 2027 submission #1555 (October 2026), Theorem 11, printed p.10 (PDF p.11); proof and Appendix B, printed pp.10–11,14–15 (PDF pp.11–12,15–16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1555.pdf; pinned PDF SHA256 1f5fce093155b2721073a124d87a3c6947269ff7851c61301dfa6e81232f0b2c

import Definitions.Def_AggregatedCodeTesting_Testing_Supplement_Computation

set_option autoImplicit false
open Finset

namespace AggregatedCodeTesting.Testing.Supplement

/-- Theorem 11 and its specified decoder and Appendix B cost. Universal preprocessing constants
precede all codes; online constants depend only on the fixed code, before width and confidence. -/
theorem theorem_11 :
    ∃ prep : MetaSearch.Heyting.Machine, ∃ a d : ℕ, 0 < a ∧
      RealizesPreprocessing prep a d ∧ RealizesAllPreprocessing prep a d ∧
      ∀ m (C : Submodule (ZMod 2) (Word m)), HasNoZeroCoord C → 0 < sStar C →
        sStar C ≠ ⊤ ∧
        ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∃ w0 : ℕ, 1 ≤ w0 ∧
        ∃ online : MetaSearch.Heyting.Machine, ∃ ac dc P : ℕ,
          0 < ac ∧ P = preprocessingBudget C a d ∧
          RealizesRecovery C online ac dc ∧
          (∀ w R : ℕ, 1 ≤ w → 1 ≤ R → Odd R →
            ∀ xs : Fin (batchSize C w * R) → (Fin m → Fin (w + 1)),
              ValidOutput C w (recovery C w R xs)) ∧
          (∀ w : ℕ, 1 ≤ w → ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 8 →
            ∃ R : ℕ, 1 ≤ R ∧ Odd R ∧
              4 * Real.log (2 * ((momentIndices C).card : ℝ) / eta) ≤ (R : ℝ) ∧
              ((batchSize C w * R : ℕ) : ℝ) ≤
                K * (w : ℝ) ^ (sStar C).toNat * Real.log (1 / eta) ∧
              ErrorAtMost C w (batchSize C w * R)
                (deterministicEstimator C (recovery C w R)) eta) ∧
          (∀ w : ℕ, w0 ≤ w → ∀ eta : ℝ, 0 < eta → eta ≤ 1 / 8 →
            ∀ N : ℕ, ∀ E : Estimator C w N, ErrorAtMost C w N E eta →
              c * (w : ℝ) ^ (sStar C).toNat * Real.log (1 / eta) ≤ (N : ℝ)) := by sorry

end AggregatedCodeTesting.Testing.Supplement
