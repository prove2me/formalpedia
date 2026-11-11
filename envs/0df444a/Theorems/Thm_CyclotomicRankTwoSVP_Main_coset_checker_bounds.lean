-- Prove2me | Theorems.Thm_CyclotomicRankTwoSVP_Main_coset_checker_bounds
-- name    : CyclotomicRankTwoSVP.Main.coset_checker_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:53:04.543321+00:00
-- url     : https://prove2.me/theorems/8fe4fec6-cb65-473c-a3da-cd55214f7300
-- title:
--   Corollary 4.5 — two-sided checker bounds in every allowed coset
-- statement:
--   There are sufficiently large absolute positive integers $C_0,k_0$, chosen before $k,q,M,n,A,\alpha$, such that the assertion holds for all $k\ge k_0$ and odd primes $q\ge(2k)^{C_0}$. For the source construction, $A\in\{0,1\}^{M\times n}$ has three ones per column, $M,n\ge1$, and no zero row. The integer positions $\alpha_1<\cdots<\alpha_n$ are Sidon, $W=|I|=3n$, $\beta_i=(2\alpha_\star+1)i$, and $q>4\beta_M$. Assume $n+2\le\lfloor\sqrt{k}\rfloor$. Let $c\in O_K$ be any element possessing an integer coefficient representative with coefficient sum $h$. For every Boolean selection $\xi$, there exists an admissible Boolean vector $x$ of weight $h$ with $[x]\in c+\mathfrak a_{q,k}$ and $x_{\alpha_j}=\xi_j$ for every $j$, and
--
--   $$B_0+2\kappa\|A\xi-1_M\|_2^2\ \le\ \frac{N(U[x]-V)}{Q^2}\ \le\ B_0+2\kappa\|A\xi-1_M\|_2^2+\frac\kappa8.$$
--
--   Both inequalities and the additive $\kappa/8$ are retained. The center here is general subject to the stated representative condition, rather than restricted to the special center used in Section 5. This packages the coset witness and checker bounds.
--
--   Differences from the source:
--   - encoding: K = Q(zeta_q), O_K = Z[zeta_q], all complex embeddings → a fixed isomorphic cyclotomic splitting field, the integer adjoin of its primitive root, and all rational algebra embeddings into C; reason: the same prime-conductor field and unnormalized canonical norm, with no additional source hypotheses
--   - encoding: one sufficiently large absolute pair C_0,k_0 → existential positive integer thresholds before every k,q and every instance; reason: taking maxima of the finitely many threshold witnesses supplies one common pair; increasing either threshold preserves each domain-restricted conclusion
--   - encoding: indices [r] = {1,...,r} and field elements F_q → Fin r and ZMod q; beta uses the row index plus one; reason: finite reindexing changes no instance or ordered pair
--   - generalization: the Sidon positions supplied by Lemma 2.3 in the construction of Section 4.1 → any strictly increasing nonnegative integer Sidon sequence satisfying q > 4 beta_M, without a quadratic size bound or algorithmic provenance; reason: the source positions satisfy these hypotheses; the separation, checker, counting and norm arguments use only the Sidon property and the stated separation bound, so every source instance is included
-- source:
--   Jiaqi Liu, Yansong Feng, Yanbin Pan, SVP Is NP-Hard for Some Rank-2 Cyclotomic Modules, STOC 2027 submission #1423 (October 2026), printed p. 19 / PDF p. 20, Corollary 4.5

import Mathlib
import Definitions.Def_CyclotomicRankTwoSVP_Main_Checker

namespace CyclotomicRankTwoSVP.Main
open scoped BigOperators

theorem coset_checker_bounds :
    ∃ C₀ k₀ : ℕ, 1 ≤ C₀ ∧ 1 ≤ k₀ ∧
      ∀ (k q : ℕ) [Fact q.Prime], Odd q → parameterDomain C₀ k₀ k q →
        ∀ (M n : ℕ) (A : Incidence M n), IsX3C A → Nondegenerate A →
          ∀ α : Fin n → ℕ, IsSidon α → 4 * beta α M < q →
            n + 2 ≤ Nat.sqrt k →
            ∀ c : K q, c ∈ OK q →
              (∃ z : ZMod q → ℤ, evalZ z = c ∧ coeffSum z = h k) →
              ∀ ξ : Fin n → Bool, ∃ x : ZMod q → Bool,
                admissible A α x ∧ weight x = h k ∧
                evalZ (bitsZ x) - c ∈ idealSet q k ∧ selected α x = ξ ∧
                B₀ q k A + 2 * kappa q k A * residual A ξ ≤ checkerSquared k A α x ∧
                checkerSquared k A α x ≤ B₀ q k A + 2 * kappa q k A * residual A ξ + kappa q k A / 8 := by sorry

end CyclotomicRankTwoSVP.Main
