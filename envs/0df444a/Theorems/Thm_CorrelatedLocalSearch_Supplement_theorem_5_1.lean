-- Prove2me | Theorems.Thm_CorrelatedLocalSearch_Supplement_theorem_5_1
-- name    : CorrelatedLocalSearch.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:08:42.466208+00:00
-- url     : https://prove2.me/theorems/00f1bc1c-72b3-47f0-8ec6-7beea954faf2
-- title:
--   Theorem 5.1 — verified search with correlated errors
-- statement:
--   For any ordered predecessor tree, $D\ge1$, $0<\eta<1$, $s\in[s_c,1]$ and primitive-error law satisfying (14), the exact Appendix F walk halts almost surely, returns the predecessor with error at most $\eta$, and uses
--   $$\mathbb E_\nu Q\le C_p\min\{K^3,K/(s-s_c)\},\qquad K=h+\log D+\log(1/\eta)+1.$$
--   The algorithm is chosen without the correct leaf depth or a tree-height bound; every move makes all $3\ell(p)$ primitive queries, including prescribed dummies.
--
--   Differences from the source:
--   - encoding: $K/(s-s_c)$ with division-by-zero convention → a cubic bound always and a linear-over-margin bound when $s>s_c$; reason: their conjunction is exactly the stated minimum with the second branch infinite at criticality
--   - encoding: an ordered predecessor tree and the Appendix F walk described in prose → explicit half-open child intervals and a block-by-block state recursion consuming all three majority blocks, including dummies; reason: this makes the source's exact algorithm binding without changing any run
--   - encoding: expectation of a possibly infinite query count → an `ENNReal` lower Lebesgue integral of an infinity-valued natural query count; reason: nonintegrability gives infinity rather than a default value
-- source:
--   Xu, Local Search with Correlated Randomness, arXiv:2607.17469 (sha256 17e00d69…), Theorem 5.1, p.14 (PDF p.16), schedule App. F pp.40–41 (PDF pp.42–43)

import Mathlib
import Definitions.Def_CorrelatedLocalSearch_Supplement_VerifiedSearch

set_option autoImplicit false

namespace CorrelatedLocalSearch.Supplement

open MeasureTheory
open scoped ENNReal BigOperators

/-- Xu, arXiv:2607.17469 (sha256 17e00d69…), Theorem 5.1, p.14 (PDF p.16), with the
exact Appendix F schedule. For every ordered tree, the algorithm is chosen without the correct
depth or a height bound; it returns the predecessor with error at most `eta` and has the full
cubic-to-linear primitive-query expectation. -/
theorem theorem_5_1 (p : Real) (hp0 : 1 / 2 < p) (hp1 : p < 1) :
    ∃ C : Real, 0 < C ∧
      ∀ tree : OrderedSearchTree, ∀ D : Real, 1 ≤ D -> ∀ eta : Real, 0 < eta -> eta < 1 ->
        IsOrderedPredecessorTree tree ->
        ∃ A : VerifiedSearchAlgorithm tree,
          UsesAppendixFSchedule p D eta A ∧
          ∀ target correct h, (∃ u : tree.Node, tree.leafLabel u = some correct ∧
              tree.depth u = h ∧ TargetInLeafInterval tree u target) ->
            ∀ s, searchThreshold p ≤ s -> s ≤ 1 ->
              ∀ nu : Measure (Nat -> Bool), nu ∈ SourceClass (errorPi p) s D ->
                nu {omega | A.queries target omega = ⊤} = 0 ∧
                nu {omega | A.answer target omega ≠ some correct} ≤ ENNReal.ofReal eta ∧
                let K := (h : Real) + Real.log D + Real.log (1 / eta) + 1
                (∫⁻ omega, ((A.queries target omega : ℕ∞) : ENNReal) ∂nu) ≤
                    ENNReal.ofReal (C * K ^ 3) ∧
                  (0 < s - searchThreshold p ->
                    (∫⁻ omega, ((A.queries target omega : ℕ∞) : ENNReal) ∂nu) ≤
                      ENNReal.ofReal (C * K / (s - searchThreshold p))) := by sorry

end CorrelatedLocalSearch.Supplement
