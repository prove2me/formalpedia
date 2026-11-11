-- Prove2me | Theorems.Thm_CyclotomicRankTwoSVP_Main_offset_separation
-- name    : CyclotomicRankTwoSVP.Main.offset_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:55.021215+00:00
-- url     : https://prove2.me/theorems/48a9a812-2c3e-4b30-a14f-181b984f9656
-- title:
--   Lemma 4.1 — separation of checker offsets
-- statement:
--   For the source construction, $A\in\{0,1\}^{M\times n}$ has three ones per column, $M,n\ge1$, and no zero row. The integer positions $\alpha_1<\cdots<\alpha_n$ are Sidon, $W=|I|=3n$, $\beta_i=(2\alpha_\star+1)i$, and $q>4\beta_M$. For every odd prime $q$ under this bound, all $2W$ signed offsets $d_{ij},-d_{ij}$ for $(i,j)\in I$ are nonzero and pairwise distinct. In addition,
--
--   $$0\notin D_{\rm bad},\qquad D_{\rm bad}\cap D_{\rm wit}=\varnothing,\qquad |D_{\rm bad}|\le2W^2=18n^2.$$
--
--   The cardinality bounds instantiate the source's $O(W^2)=O(n^2)$ by bounding each of the two defining images by $W^2$. Incidence sums include equal incidences, and the signed-offset injectivity quantifies over the incidence and sign together. These facts separate the correlations used by the checker.
--
--   Differences from the source:
--   - encoding: indices [r] = {1,...,r} and field elements F_q → Fin r and ZMod q; beta uses the row index plus one; reason: finite reindexing changes no instance or ordered pair
--   - encoding: O(W^2)=O(n^2) → the simultaneous bounds |D_bad| <= 2 W^2 and |D_bad| <= 18 n^2; reason: each defining image has at most W^2 elements, and the three-ones condition gives W=3n, as in the proof
--   - generalization: the Sidon positions supplied by Lemma 2.3 in the construction of Section 4.1 → any strictly increasing nonnegative integer Sidon sequence satisfying q > 4 beta_M, without a quadratic size bound or algorithmic provenance; reason: the source positions satisfy these hypotheses; the separation, checker, counting and norm arguments use only the Sidon property and the stated separation bound, so every source instance is included
-- source:
--   Jiaqi Liu, Yansong Feng, Yanbin Pan, SVP Is NP-Hard for Some Rank-2 Cyclotomic Modules, STOC 2027 submission #1423 (October 2026), printed p. 15 / PDF p. 16, Lemma 4.1

import Mathlib
import Definitions.Def_CyclotomicRankTwoSVP_Main_Checker

namespace CyclotomicRankTwoSVP.Main
open scoped BigOperators

theorem offset_separation (q M n : ℕ) [Fact q.Prime] (hq : Odd q)
    (A : Incidence M n) (hA : IsX3C A) (hnd : Nondegenerate A)
    (α : Fin n → ℕ) (hα : IsSidon α) (hsep : 4 * beta α M < q) :
    (∀ ij ∈ incidences A, offset q α ij ≠ 0 ∧ -offset q α ij ≠ 0) ∧
    (Function.Injective fun p : {ij // ij ∈ incidences A} × Bool =>
      if p.2 then offset q α p.1.val else -offset q α p.1.val) ∧
    0 ∉ Dbad q A α ∧ Disjoint (Dbad q A α) (Dwit q α) ∧
    (Dbad q A α).card ≤ 2 * W A ^ 2 ∧ (Dbad q A α).card ≤ 18 * n ^ 2 := by sorry

end CyclotomicRankTwoSVP.Main
