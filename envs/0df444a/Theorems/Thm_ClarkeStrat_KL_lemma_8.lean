-- Prove2me | Theorems.Thm_ClarkeStrat_KL_lemma_8
-- name    : ClarkeStrat.KL.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:13.933203+00:00
-- url     : https://prove2.me/theorems/40f59a74-3f28-40c9-8b8d-3850cff78416
-- title:
--   Lemma 8, p. 564 — nonvertical definable C^p-Whitney stratification of Graph f, compatible with given definable sets
-- statement:
--   Let $\mathcal O$ be an o-minimal structure on $(\mathbb R,+,\cdot)$, let $B_1,\dots,B_q$ be definable subsets of $\mathbb R^n$, and let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be a definable lower semicontinuous function. Then for every integer $p\ge 1$ there is a finite family $S_1,\dots,S_\ell$ of definable subsets of $\mathbb R^{n+1}$ such that
--
--   1. $(S_i)$ is a nonvertical $C^p$-Whitney stratification of $\operatorname{Graph} f$;
--   2. the projections $X_i=\Pi(S_i)\subseteq\mathbb R^n$ form a $C^p$-Whitney stratification of $\operatorname{dom} f$;
--   3. this stratification is compatible with $\{B_1,\dots,B_q\}$:
--   $$B_j\cap\operatorname{dom} f=\bigcup_{i\in J_j}X_i\qquad\text{for some } J_j\subseteq\{1,\dots,\ell\},\ j=1,\dots,q.$$
--
--   This is the bridge between o-minimal geometry and the projection formula of §3: every definable lower semicontinuous function satisfies the hypotheses of Proposition 4.
--
--   **Formalization Note** The paper defines compatibility only for subsets of the stratified set, while $B_j$ need not lie in $\operatorname{dom} f$; compatibility is read as "$B_j\cap\operatorname{dom} f$ is a union of strata" (with finitely many strata, local finiteness of the union is automatic). $f$ is assumed never equal to $-\infty$.
-- source:
--   Bolte, Daniilidis, Lewis & Shiota, Clarke subgradients of stratifiable functions, SIAM J. Optim. 18(2) (2007), p. 564, Lemma 8

import Mathlib
import Definitions.Def_ClarkeStrat_KL_Setting

open Filter Topology
open scoped Pointwise InnerProductSpace
open NonconvexSplitting.Shared

namespace ClarkeStrat.KL

/-- Lemma 8, p. 564: for definable sets `B₁, …, B_q ⊆ ℝⁿ` and a definable lower semicontinuous
`f : ℝⁿ → ℝ ∪ {+∞}`, for every `p ≥ 1` there is a nonvertical definable `C^p`-Whitney stratification
`S₁, …, S_ℓ` of `Graph f` whose projections `X_i = Π(S_i)` form a `C^p`-Whitney stratification of
`dom f` compatible with the `B_j` (each `B_j ∩ dom f` is a union of strata). -/
theorem lemma_8 (O : OMinimalStructure) {n : ℕ} {q : ℕ}
    (B : Fin q → Set (EuclideanSpace ℝ (Fin n))) (hB : ∀ j, B j ∈ O.O n)
    (f : EuclideanSpace ℝ (Fin n) → EReal) (hbot : ∀ x, f x ≠ ⊥) (hlsc : LowerSemicontinuous f)
    (hdef : graphSet f ∈ O.O (n + 1)) (p : ℕ) (hp : 1 ≤ p) :
    ∃ (ℓ : ℕ) (S : Fin ℓ → Set (EuclideanSpace ℝ (Fin (n + 1)))),
      (∀ i, S i ∈ O.O (n + 1)) ∧ IsCpStratification p (graphSet f) S ∧ WhitneyA S ∧
      IsNonvertical S ∧
      IsCpStratification p {x | f x ≠ ⊤} (fun i => (projL '' S i : Set (EuclideanSpace ℝ (Fin n)))) ∧
      WhitneyA (fun i => (projL '' S i : Set (EuclideanSpace ℝ (Fin n)))) ∧
      ∀ j, ∃ J : Finset (Fin ℓ), B j ∩ {x | f x ≠ ⊤} = ⋃ i ∈ J, projL '' S i := by sorry

end ClarkeStrat.KL
