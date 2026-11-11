-- Prove2me | Theorems.Thm_CyclotomicRankTwoSVP_Main_multiplication_bounds
-- name    : CyclotomicRankTwoSVP.Main.multiplication_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:57.075571+00:00
-- url     : https://prove2.me/theorems/62340a75-a4b9-42c4-962f-5e61a3f5662e
-- title:
--   Lemma 4.2 — checker multiplication bounds
-- statement:
--   There are sufficiently large absolute positive integers $C_0,k_0$, chosen before $k,q,M,n,A,\alpha$, such that the assertion holds for all $k\ge k_0$ and odd primes $q\ge(2k)^{C_0}$. For the source construction, $A\in\{0,1\}^{M\times n}$ has three ones per column, $M,n\ge1$, and no zero row. The integer positions $\alpha_1<\cdots<\alpha_n$ are Sidon, $W=|I|=3n$, $\beta_i=(2\alpha_\star+1)i$, and $q>4\beta_M$. Use $h=\lfloor21k/20\rfloor$, $Q=128W^4h$, $g=\sum_{(i,j)\in I}(\zeta^{d_{ij}}+\zeta^{-d_{ij}})$, $U=Q+g^2$ and $V=6\sum_j\zeta^{\alpha_j}$. For every pair $y,w\in K$,
--
--   $$\sqrt{N(Uy)}\ge Q\sqrt{N(y)},\qquad\sqrt{N(Vw)}\le2W\sqrt{N(w)}.$$
--
--   There is no integrality or ideal-coset constraint on these scalars. These are bounds in the canonical norm for the concrete checker multipliers, with the source constants unchanged.
--
--   Differences from the source:
--   - encoding: K = Q(zeta_q), O_K = Z[zeta_q], all complex embeddings → a fixed isomorphic cyclotomic splitting field, the integer adjoin of its primitive root, and all rational algebra embeddings into C; reason: the same prime-conductor field and unnormalized canonical norm, with no additional source hypotheses
--   - encoding: one sufficiently large absolute pair C_0,k_0 → existential positive integer thresholds before every k,q and every instance; reason: taking maxima of the finitely many threshold witnesses supplies one common pair; increasing either threshold preserves each domain-restricted conclusion
--   - encoding: indices [r] = {1,...,r} and field elements F_q → Fin r and ZMod q; beta uses the row index plus one; reason: finite reindexing changes no instance or ordered pair
--   - generalization: the Sidon positions supplied by Lemma 2.3 in the construction of Section 4.1 → any strictly increasing nonnegative integer Sidon sequence satisfying q > 4 beta_M, without a quadratic size bound or algorithmic provenance; reason: the source positions satisfy these hypotheses; the separation, checker, counting and norm arguments use only the Sidon property and the stated separation bound, so every source instance is included
-- source:
--   Jiaqi Liu, Yansong Feng, Yanbin Pan, SVP Is NP-Hard for Some Rank-2 Cyclotomic Modules, STOC 2027 submission #1423 (October 2026), printed p. 16 / PDF p. 17, Lemma 4.2

import Mathlib
import Definitions.Def_CyclotomicRankTwoSVP_Main_Checker

namespace CyclotomicRankTwoSVP.Main
open scoped BigOperators

theorem multiplication_bounds :
    ∃ C₀ k₀ : ℕ, 1 ≤ C₀ ∧ 1 ≤ k₀ ∧
      ∀ (k q : ℕ) [Fact q.Prime], Odd q → parameterDomain C₀ k₀ k q →
        ∀ (M n : ℕ) (A : Incidence M n), IsX3C A → Nondegenerate A →
          ∀ α : Fin n → ℕ, IsSidon α → 4 * beta α M < q →
            ∀ y w : K q,
              Real.sqrt (N (U k A α * y)) ≥ Q k A * Real.sqrt (N y) ∧
              Real.sqrt (N (V α * w)) ≤ 2 * W A * Real.sqrt (N w) := by sorry

end CyclotomicRankTwoSVP.Main
