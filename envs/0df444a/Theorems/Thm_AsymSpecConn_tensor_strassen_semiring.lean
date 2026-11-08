-- Prove2me | Theorems.Thm_AsymSpecConn_tensor_strassen_semiring
-- name    : AsymSpecConn.tensor_strassen_semiring
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:41:10.84091+00:00
-- url     : https://prove2.me/theorems/35e4cdbc-0a09-45c5-9998-4e61e2313195
-- title:
--   §3, p.21 — $\mathcal S_F$ with restriction is a Strassen semiring
-- statement:
--   Let $F$ be a field and $k\ge2$. The set $\mathcal S_F$ of $k$-tensors over $F$ up to equivalence, with direct sum, Kronecker product and the restriction preorder, and with $m\in\mathbb N$ interpreted as the class of the unit tensor $\langle m\rangle=\sum_{j=1}^m e_j\otimes\dots\otimes e_j$, is a Strassen semiring: addition and multiplication preserve the preorder, the natural numbers carry their usual order, and for nonzero $s,t$ there is an integer $m\ge1$ with $s\le mt$.
--
--   This is what places tensors in the scope of the abstract theory of the source's §2.
--
--   Differences from the source:
--
--   - encoding: S_F, k-tensors over F up to equivalence, with legs V_1,…,V_k → MME.TensorQ with legs indexed by Fin k (0-based) in one universe; reason: Lean convention; every finite-dimensional space has an isomorphic copy in that universe
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), §3, p.21

import Mathlib
import Definitions.Def_mme_tensor_quotient
import Definitions.Def_AsymSpecConn_IsStrassenSemiring
import Definitions.Def_AsymSpecConn_tensorPreorder

set_option autoImplicit false

namespace AsymSpecConn

/-- **§3, p.21** of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…): "Let SF be the set of k-tensors over F up to
equivalence, with ⊕, ⊗ and ≤, all of which are well defined on equivalence classes. For m ∈ N, the
element m of SF is the class of the unit tensor ⟨m⟩ = Σ_{j=1}^m ej ⊗ ⋯ ⊗ ej. This is a Strassen
semiring, and we write ∆F for its asymptotic spectrum."

**Formalization Note** `S_F` is the published `MME.TensorQ F k` (classes of `MME.TensorObj F k`
under mutual restriction; `+` is the direct sum, `*` the Kronecker product, `(m : S_F)` the class
of the unit tensor `⟨m⟩`) with the restriction preorder `tensorPreorder F hk`. "Strassen semiring"
is the paper's notion of §2 (`IsStrassenSemiring`). Every field `F`, as printed; `k ≥ 2` is the
standing assumption of §3. -/
theorem tensor_strassen_semiring (F : Type*) [Field F] {k : ℕ} (hk : 2 ≤ k) :
    IsStrassenSemiring (MME.TensorQ F k) (tensorPreorder F hk) := by sorry

end AsymSpecConn
