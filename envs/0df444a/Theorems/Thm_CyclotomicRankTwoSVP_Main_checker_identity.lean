-- Prove2me | Theorems.Thm_CyclotomicRankTwoSVP_Main_checker_identity
-- name    : CyclotomicRankTwoSVP.Main.checker_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:55.100714+00:00
-- url     : https://prove2.me/theorems/aee91a25-d89e-46df-949c-f2c01ee9a78c
-- title:
--   Theorem 4.3 — checker identity, nonnegative error and remainder
-- statement:
--   There are sufficiently large absolute positive integers $C_0,k_0$, chosen before $k,q,M,n,A,\alpha$, such that the assertion holds for all $k\ge k_0$ and odd primes $q\ge(2k)^{C_0}$. For the source construction, $A\in\{0,1\}^{M\times n}$ has three ones per column, $M,n\ge1$, and no zero row. The integer positions $\alpha_1<\cdots<\alpha_n$ are Sidon, $W=|I|=3n$, $\beta_i=(2\alpha_\star+1)i$, and $q>4\beta_M$. Every Boolean vector $x\in\{0,1\}^{\mathbb F_q}$ of weight $h$ determines $\xi_j=x_{\alpha_j}$. Set $\kappa=2q/Q$, $R(x)=N(g^2[x]-V)/Q^2$ and
--
--   $$B_0=H+\kappa\left(2Wh-2M+\frac{2hW-4h^2W^2}{q}\right).$$
--
--   For the actual error $E(x)$ defined by the three correlation sums in (19),
--
--   $$E(x)\ge0,\qquad\frac{N(U[x]-V)}{Q^2}=B_0+2\kappa\|A\xi-1_M\|_2^2+\kappa E(x)+R(x),$$
--   $$0\le R(x)<\kappa/8.$$
--
--   The constant $B_0$ is rational and independent of $x$; rationality is also an explicit conclusion. The first error sum uses real subtraction of the designated pair's contribution; the other two sum over ordered incidences, including repeated incidences in the sum-offset term. Thus the nonnegative error is connected to its actual formula, so admissibility can make it vanish.
--
--   Differences from the source:
--   - encoding: K = Q(zeta_q), O_K = Z[zeta_q], all complex embeddings → a fixed isomorphic cyclotomic splitting field, the integer adjoin of its primitive root, and all rational algebra embeddings into C; reason: the same prime-conductor field and unnormalized canonical norm, with no additional source hypotheses
--   - encoding: one sufficiently large absolute pair C_0,k_0 → existential positive integer thresholds before every k,q and every instance; reason: taking maxima of the finitely many threshold witnesses supplies one common pair; increasing either threshold preserves each domain-restricted conclusion
--   - encoding: indices [r] = {1,...,r} and field elements F_q → Fin r and ZMod q; beta uses the row index plus one; reason: finite reindexing changes no instance or ordered pair
--   - encoding: there exists E(x)>=0, with the proof defining it by (19) → nonnegativity and the identity for the explicit expression (19); reason: identifies the source witness rather than assuming an unconstrained error variable
--   - generalization: the Sidon positions supplied by Lemma 2.3 in the construction of Section 4.1 → any strictly increasing nonnegative integer Sidon sequence satisfying q > 4 beta_M, without a quadratic size bound or algorithmic provenance; reason: the source positions satisfy these hypotheses; the separation, checker, counting and norm arguments use only the Sidon property and the stated separation bound, so every source instance is included
-- source:
--   Jiaqi Liu, Yansong Feng, Yanbin Pan, SVP Is NP-Hard for Some Rank-2 Cyclotomic Modules, STOC 2027 submission #1423 (October 2026), printed p. 16 / PDF p. 17, Theorem 4.3

import Mathlib
import Definitions.Def_CyclotomicRankTwoSVP_Main_Checker

namespace CyclotomicRankTwoSVP.Main
open scoped BigOperators

theorem checker_identity :
    ∃ C₀ k₀ : ℕ, 1 ≤ C₀ ∧ 1 ≤ k₀ ∧
      ∀ (k q : ℕ) [Fact q.Prime], Odd q → parameterDomain C₀ k₀ k q →
        ∀ (M n : ℕ) (A : Incidence M n), IsX3C A → Nondegenerate A →
          ∀ α : Fin n → ℕ, IsSidon α → 4 * beta α M < q →
            (∃ b : ℚ, (b : ℝ) = B₀ q k A) ∧
            ∀ x : ZMod q → Bool, weight x = h k →
              0 ≤ errorTerm A α x ∧
              checkerSquared k A α x = B₀ q k A +
                2 * kappa q k A * residual A (selected α x) +
                kappa q k A * errorTerm A α x + remainder k A α x ∧
              0 ≤ remainder k A α x ∧ remainder k A α x < kappa q k A / 8 := by sorry

end CyclotomicRankTwoSVP.Main
