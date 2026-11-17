-- Prove2me | Theorems.Thm_CoRSuccGap_Supplement_theorem_7_3
-- name    : CoRSuccGap.Supplement.theorem_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:42:41.849399+00:00
-- url     : https://prove2.me/theorems/892eba92-57f0-4528-b9b7-49dd60dae5f7
-- title:
--   Theorem 7.3 -- exponential arity-elimination overhead over idempotent semirings
-- statement:
--   Let $S$ be a nontrivial commutative semiring with idempotent addition and finite join breadth $\beta$. For every $k\ge1$, $G_k$ has a positive $ARA(3)$ expression of size $O(k)$, while every typed matrix circuit computing it on all finite nonempty inputs satisfies
--
--   $$
--   \beta\bigl(\#_{mv}(C)+3\#_{mm}(C)\bigr)\ge2^k.
--   $$
--
--   Consequently the circuit has at least $2^k/(3\beta)$ charged aggregation gates. Conversely, a typed matrix circuit with exactly $2^k$ matrix--vector contractions and no matrix--matrix contractions computes $G_k$; its remaining gates are entrywise operations or broadcasts.
--
--   Differences from the source:
--   - encoding: finite join breadth is described as the least number of indispensable summands → Lean defines the finite-subjoin property and its leastness explicitly; reason: direct proposition-valued rendering of the definition.
--   - generalization: positivity of the breadth is implicit for a nontrivial semiring → Lean also returns $0<\beta$ as an explicit conclusion; reason: it is forced by the source hypotheses and makes the displayed real division nondegenerate.
-- source:
--   Uezato--Nakamura, arXiv:2609.26778 (held version, sha256 5ad6337d...), Theorem 7.3, p.42 (PDF 44); models and breadth Sections 7.1--7.3, pp.37--41 (PDF 39--43)

import Definitions.Def_CoRSuccGap_Supplement_TypedMatrixCircuit

set_option autoImplicit false

namespace CoRSuccGap
namespace Supplement

/-- **Theorem 7.3 (Exponential arity-elimination overhead).** Uezato--Nakamura,
*An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of Relations*,
arXiv:2609.26778 (held version, sha256 5ad6337d…c9b6), Theorem 7.3, p.42 (PDF 44).

For every nontrivial commutative semiring with idempotent addition and finite join breadth `β`,
the semiring query `G_k` has a positive ARA(3) expression of size `O(k)`.  Every fixed-wiring typed
matrix circuit computing it on all finite nonempty inputs satisfies
`β (#mv + 3 #mm) ≥ 2^k`, hence has at least `2^k/(3β)` charged aggregation gates.  Conversely,
there is a circuit using exactly `2^k` matrix--vector contractions and no matrix--matrix contraction.

**Formalization Note.** `HasJoinBreadth S β` says both that `β` is a finite join bound and that it
is the least such bound.  The conclusion records `0 < β`, forced by nontriviality, before using real
division.  The ARA constant is chosen after the fixed semiring but before `k`. -/
theorem theorem_7_3 :
    ∀ (S : Type) [CommSemiring S] [Nontrivial S],
      (∀ a : S, a + a = a) → ∀ β : ℕ, HasJoinBreadth S β →
      ∃ c : ℕ, 0 < c ∧ 0 < β ∧ ∀ k : ℕ, 1 ≤ k →
        (∃ e : ARA3Expr (GSym k), ARA3RepresentsGk S k e ∧ e.numNodes ≤ c * k) ∧
        (∀ C : TypedMatrixCircuit S k, C.ComputesGk →
          2 ^ k ≤ β * (C.numMV + 3 * C.numMM) ∧
          (2 ^ k : ℝ) / (3 * β : ℝ) ≤ (C.numMV + C.numMM : ℕ)) ∧
        ∃ C : TypedMatrixCircuit S k,
          C.ComputesGk ∧ C.numMV = 2 ^ k ∧ C.numMM = 0 := by sorry

end Supplement
end CoRSuccGap
