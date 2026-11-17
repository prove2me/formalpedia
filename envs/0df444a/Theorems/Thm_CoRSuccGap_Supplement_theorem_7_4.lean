-- Prove2me | Theorems.Thm_CoRSuccGap_Supplement_theorem_7_4
-- name    : CoRSuccGap.Supplement.theorem_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T00:44:05.451724+00:00
-- url     : https://prove2.me/theorems/79853dec-9184-4ff5-86ad-0ee0eb896fe2
-- title:
--   Theorem 7.4 -- Boolean arity-elimination overhead
-- statement:
--   Let $k\ge1$. Over the Boolean semiring, every typed matrix circuit computing $G_k$ on all finite nonempty inputs satisfies the sharper bound
--
--   $$
--   \#_{mv}(C)+2\#_{mm}(C)\ge2^k.
--   $$
--
--   The circuit model includes arbitrary uniform entrywise functions and arbitrary fixed aggregation kernels $\kappa:\mathbb B^2\to\mathbb B$; kernels need not be associative, monotone or zero-preserving. All non-aggregation operations, vector inner products and singleton-index contractions remain uncharged.
--
--   Differences from the source:
--   - encoding: the Boolean semiring $\mathbb B=\{0,1\}$ is written abstractly → Lean realizes it as the powerset semiring of a singleton, with union and set product; reason: this is a two-element commutative idempotent semiring isomorphic to $(\{0,1\},\lor,\land)$.
-- source:
--   Uezato--Nakamura, arXiv:2609.26778 (held version, sha256 5ad6337d...), Theorem 7.4, p.43 (PDF 45)

import Definitions.Def_CoRSuccGap_Supplement_TypedMatrixCircuit

set_option autoImplicit false

namespace CoRSuccGap
namespace Supplement

/-- **Theorem 7.4 (Boolean arity-elimination overhead).** Uezato--Nakamura,
*An Exponential Succinctness Gap between Three-Variable Logic and the Calculus of Relations*,
arXiv:2609.26778 (held version, sha256 5ad6337d…c9b6), Theorem 7.4, p.43 (PDF 45).

Over the Boolean semiring, every typed matrix circuit computing `G_k` on every finite nonempty
input satisfies `#mv + 2 #mm ≥ 2^k`.  `TypedMatrixCircuit` permits arbitrary uniform entrywise
functions and an arbitrary fixed binary kernel at each contraction gate; neither is required to be
associative, monotone, or zero-preserving. -/
theorem theorem_7_4 (k : ℕ) (hk : 1 ≤ k) (C : TypedMatrixCircuit BoolSemiring k)
    (hC : C.ComputesGk) :
    2 ^ k ≤ C.numMV + 2 * C.numMM := by sorry

end Supplement
end CoRSuccGap
