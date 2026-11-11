-- Prove2me | Theorems.Thm_CyclotomicRankTwoSVP_Main_admissible_representatives
-- name    : CyclotomicRankTwoSVP.Main.admissible_representatives
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:47.092135+00:00
-- url     : https://prove2.me/theorems/05735365-8ce3-4788-854a-3d622a340cb5
-- title:
--   Theorem 4.4 — admissible representatives for every syndrome
-- statement:
--   There are sufficiently large absolute positive integers $C_0,k_0$, chosen before $k,q,M,n,A,\alpha$, such that the assertion holds for all $k\ge k_0$ and odd primes $q\ge(2k)^{C_0}$. For the source construction, $A\in\{0,1\}^{M\times n}$ has three ones per column, $M,n\ge1$, and no zero row. The integer positions $\alpha_1<\cdots<\alpha_n$ are Sidon, $W=|I|=3n$, $\beta_i=(2\alpha_\star+1)i$, and $q>4\beta_M$. Assume additionally $n+2\le\lfloor\sqrt{k}\rfloor$. For every $u\in\mathbb F_q^k$ with $u_0=h\pmod q$ and every Boolean selection $\xi\in\{0,1\}^n$, there exists a Boolean vector $x$ such that
--
--   $$H_q(k)x=u,\qquad\sum_a x_a=h,\qquad x_{\alpha_j}=\xi_j\quad(1\le j\le n).$$
--
--   It is admissible: every witness-offset correlation is exactly $\xi_j\xi_\ell$, and every bad-offset correlation vanishes, as in (20). The quantifiers retain all compatible syndromes and all prescribed assignments. This is an existence theorem for completeness witnesses, with no claim that the reduction computes such a representative.
--
--   Differences from the source:
--   - encoding: one sufficiently large absolute pair C_0,k_0 → existential positive integer thresholds before every k,q and every instance; reason: taking maxima of the finitely many threshold witnesses supplies one common pair; increasing either threshold preserves each domain-restricted conclusion
--   - encoding: indices [r] = {1,...,r} and field elements F_q → Fin r and ZMod q; beta uses the row index plus one; reason: finite reindexing changes no instance or ordered pair
--   - generalization: the Sidon positions supplied by Lemma 2.3 in the construction of Section 4.1 → any strictly increasing nonnegative integer Sidon sequence satisfying q > 4 beta_M, without a quadratic size bound or algorithmic provenance; reason: the source positions satisfy these hypotheses; the separation, checker, counting and norm arguments use only the Sidon property and the stated separation bound, so every source instance is included
-- source:
--   Jiaqi Liu, Yansong Feng, Yanbin Pan, SVP Is NP-Hard for Some Rank-2 Cyclotomic Modules, STOC 2027 submission #1423 (October 2026), printed p. 18 / PDF p. 19, Theorem 4.4

import Mathlib
import Definitions.Def_CyclotomicRankTwoSVP_Main_Checker

namespace CyclotomicRankTwoSVP.Main
open scoped BigOperators

theorem admissible_representatives :
    ∃ C₀ k₀ : ℕ, 1 ≤ C₀ ∧ 1 ≤ k₀ ∧
      ∀ (k q : ℕ) [Fact q.Prime], Odd q → parameterDomain C₀ k₀ k q →
        ∀ (M n : ℕ) (A : Incidence M n), IsX3C A → Nondegenerate A →
          ∀ α : Fin n → ℕ, IsSidon α → 4 * beta α M < q →
            n + 2 ≤ Nat.sqrt k →
            ∀ (u : Fin k → ZMod q), compatible k (h k) u →
              ∀ ξ : Fin n → Bool, ∃ x : ZMod q → Bool,
                admissible A α x ∧ syndrome k (bitsZ x) = u ∧ weight x = h k ∧ selected α x = ξ := by sorry

end CyclotomicRankTwoSVP.Main
