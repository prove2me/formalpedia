-- Prove2me | Theorems.Thm_AsymSpecConn_lemma_3_5
-- name    : AsymSpecConn.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:41:29.867301+00:00
-- url     : https://prove2.me/theorems/2976feae-f6d3-4be7-8eec-8b45fcae19b7
-- title:
--   Lemma 3.5 — $\mathcal S$ is $\mathcal B$-decomposable and $\mathcal A_i$-decomposable
-- statement:
--   Let $k\ge2$ and let $\mathcal S$ be the semiring of complex $k$-tensors up to equivalence. Then $\mathcal S$ is $\mathcal B$-decomposable, and $\mathcal A_i$-decomposable for every $i\in[k]$, where $\mathcal B$ is the set of jointly irreducible tensors and $\mathcal A_i$ the set of $i$-irreducible tensors.
--
--   This verifies the structural hypothesis of the abstract interpolation theorem for tensors.
--
--   Differences from the source:
--
--   - encoding: S, complex k-tensors up to equivalence, with legs V_1,…,V_k → MME.TensorQ ℂ k with legs indexed by Fin k (0-based) in Type; reason: Lean convention; every finite-dimensional space has an isomorphic copy in Type
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), Lemma 3.5, p.23

import Mathlib
import Definitions.Def_mme_tensor_quotient
import Definitions.Def_AsymSpecConn_IsADecomposable
import Definitions.Def_AsymSpecConn_tensorPreorder
import Definitions.Def_AsymSpecConn_irreducibleSet

set_option autoImplicit false

namespace AsymSpecConn

/-- **Lemma 3.5** (p.23 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)): "The semiring S is B-decomposable, and
Ai-decomposable for every i ∈ [k]."

**Formalization Note** `S = S_ℂ = MME.TensorQ ℂ k` with the restriction preorder, `k ≥ 2`;
`B = jointlyIrreducibleSet hk`, `A_i = irreducibleSet hk i`. -/
theorem lemma_3_5 {k : ℕ} (hk : 2 ≤ k) :
    IsADecomposable (tensorPreorder ℂ hk) (jointlyIrreducibleSet hk) ∧
    ∀ i : Fin k, IsADecomposable (tensorPreorder ℂ hk) (irreducibleSet hk i) := by sorry

end AsymSpecConn
