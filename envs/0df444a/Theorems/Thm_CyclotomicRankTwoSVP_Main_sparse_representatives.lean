-- Prove2me | Theorems.Thm_CyclotomicRankTwoSVP_Main_sparse_representatives
-- name    : CyclotomicRankTwoSVP.Main.sparse_representatives
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:11.076145+00:00
-- url     : https://prove2.me/theorems/0a9a93b9-17e9-4d36-9f7c-fa20e906eba6
-- title:
--   Lemma 3.5 — sparse representatives and root-of-unity gap
-- statement:
--   For every odd prime $q$, the following two assertions hold. Every $v\in O_K$ has an integer coefficient representative $z$ such that
--
--   $$[z]=v,\qquad\sum_a z_a^2\le2N(v)/q,\qquad |\operatorname{supp}z|\le2N(v)/q.$$
--
--   Every nonzero $w\in O_K$ is either a root of unity $w=\pm\zeta^j$ for some $0\le j<q$, with $N(w)=q-1$, or is not of this form and satisfies
--
--   $$N(w)\ge2q-4.$$
--
--   Both the support bound and the two-sided classification are retained. They control the short scalar multiples needed by module soundness.
--
--   Differences from the source:
--   - encoding: K = Q(zeta_q), O_K = Z[zeta_q], all complex embeddings → a fixed isomorphic cyclotomic splitting field, the integer adjoin of its primitive root, and all rational algebra embeddings into C; reason: the same prime-conductor field and unnormalized canonical norm, with no additional source hypotheses
--   - encoding: indices [r] = {1,...,r} and field elements F_q → Fin r and ZMod q; beta uses the row index plus one; reason: finite reindexing changes no instance or ordered pair
-- source:
--   Jiaqi Liu, Yansong Feng, Yanbin Pan, SVP Is NP-Hard for Some Rank-2 Cyclotomic Modules, STOC 2027 submission #1423 (October 2026), printed p. 12 / PDF p. 13, Lemma 3.5

import Mathlib
import Definitions.Def_CyclotomicRankTwoSVP_Main_Arithmetic

namespace CyclotomicRankTwoSVP.Main
open scoped BigOperators

theorem sparse_representatives (q : ℕ) [Fact q.Prime] (hq : Odd q) :
    (∀ v : K q, v ∈ OK q → ∃ z : ZMod q → ℤ, evalZ z = v ∧
      coeffNorm z ≤ 2 * N v / q ∧
      ((Finset.univ.filter fun a => z a ≠ 0).card : ℝ) ≤ 2 * N v / q) ∧
    (∀ w : K q, w ∈ OK q → w ≠ 0 →
      (((∃ j : Fin q, w = zeta q ^ j.val ∨ w = -(zeta q ^ j.val)) ∧ N w = (q : ℝ) - 1) ∨
        ((∀ j : Fin q, w ≠ zeta q ^ j.val ∧ w ≠ -(zeta q ^ j.val)) ∧ N w ≥ 2 * q - 4))) := by sorry

end CyclotomicRankTwoSVP.Main
