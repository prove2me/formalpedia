-- Prove2me | Theorems.Thm_CoRSuccGap_Supplement_theorem_1_6
-- name    : CoRSuccGap.Supplement.theorem_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:43:25.536775+00:00
-- url     : https://prove2.me/theorems/3d93104d-bb0d-4b4d-91e5-e7069945ab1d
-- title:
--   Theorem 1.6 -- tropical arity-elimination overhead
-- statement:
--   For every $k\ge1$ and for each of the min--plus semirings
--
--   $$
--   \operatorname{Trop}_{\mathbb N}=\mathbb N\cup\{+\infty\},\qquad
--   \operatorname{Trop}_{\mathbb Z}=\mathbb Z\cup\{+\infty\},
--   $$
--
--   the query $G_k$ has an $ARA(3)$ expression of size $O(k)$, but every typed matrix circuit computing it on all finite nonempty inputs satisfies
--
--   $$
--   \#_{mv}(C)+3\#_{mm}(C)\ge2^k.
--   $$
--
--   In both semirings, addition is minimum, multiplication is ordinary addition, semiring zero is $+\infty$, and semiring one is $0$.
--
--   Differences from the source:
--   - encoding: the source quantifies $S\in\{\operatorname{Trop}_{\mathbb N},\operatorname{Trop}_{\mathbb Z}\}$ → Lean states a conjunction for Mathlib's two tropical carrier types; reason: type-valued finite-set membership is represented by the two exhaustive cases.
--   - encoding: the source uses $O(k)$ → Lean uses a positive linear constant chosen before $k$ for each of the two fixed semirings; reason: explicit asymptotic quantifiers.
-- source:
--   Uezato--Nakamura, arXiv:2609.26778 (held version, sha256 5ad6337d...), Theorem 1.6, p.42 (PDF 44)

import Definitions.Def_CoRSuccGap_Supplement_TypedMatrixCircuit

set_option autoImplicit false

namespace CoRSuccGap
namespace Supplement

/-- **Theorem 1.6 (Tropical arity-elimination overhead).** Uezato--Nakamura,
*An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of Relations*,
arXiv:2609.26778 (held version, sha256 5ad6337d…c9b6), Theorem 1.6, p.42 (PDF 44).

For both the natural and integer min--plus semirings, `G_k` has a positive ARA(3) expression of
size `O(k)`, while every typed matrix circuit computing it on all finite nonempty inputs satisfies
`#mv + 3 #mm ≥ 2^k`.  The two conjuncts below state the result separately for
`ℕ∪{+∞}` and `ℤ∪{+∞}` with tropical addition `min` and multiplication ordinary addition. -/
theorem theorem_1_6 :
    (∃ c : ℕ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
      (∃ e : ARA3Expr (GSym k), ARA3RepresentsGk TropNat k e ∧ e.numNodes ≤ c * k) ∧
      ∀ C : TypedMatrixCircuit TropNat k, C.ComputesGk →
        2 ^ k ≤ C.numMV + 3 * C.numMM) ∧
    (∃ c : ℕ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k →
      (∃ e : ARA3Expr (GSym k), ARA3RepresentsGk TropInt k e ∧ e.numNodes ≤ c * k) ∧
      ∀ C : TypedMatrixCircuit TropInt k, C.ComputesGk →
        2 ^ k ≤ C.numMV + 3 * C.numMM) := by sorry

end Supplement
end CoRSuccGap
