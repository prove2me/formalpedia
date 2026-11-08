-- Prove2me | Theorems.Thm_AsymSpecConn_lemma_3_4
-- name    : AsymSpecConn.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:41:17.068023+00:00
-- url     : https://prove2.me/theorems/5a614852-5768-4cba-bdeb-9eabc562d9c7
-- title:
--   Lemma 3.4 — $\mathcal B$-decomposition of the Kronecker powers of a tensor
-- statement:
--   Let $t\in V_1\otimes\dots\otimes V_k$ be nonzero and let $n\ge1$. For every $i\in[k]$ let $\mathfrak S_n$ act on $V_i^{\otimes n}$ by permuting the factors, let
--   $$V_i^{\otimes n}=\bigoplus_{j=1}^{q_i}U^{(i)}_j$$
--   be a decomposition into irreducible $\mathfrak S_n$-subrepresentations, and let $p^{(i)}_j$ be the projection onto $U^{(i)}_j$ along the other summands. Then the nonzero tensors
--   $$a_{j_1,\dots,j_k}=(p^{(1)}_{j_1}\otimes\dots\otimes p^{(k)}_{j_k})t^{\otimes n}$$
--   give a $\mathcal B$-decomposition of $t^{\otimes n}$ of length at most $\prod_{i=1}^k(n+1)^{(\dim V_i)^2}$. Every nonzero $a_{j_1,\dots,j_k}$ is concise in $U^{(1)}_{j_1}\otimes\dots\otimes U^{(k)}_{j_k}$.
--
--   This decomposes the Kronecker powers of every tensor explicitly into jointly irreducible tensors.
--
--   Differences from the source:
--
--   - encoding: S, complex k-tensors up to equivalence, with legs V_1,…,V_k → MME.TensorQ ℂ k with legs indexed by Fin k (0-based) in Type; reason: Lean convention; every finite-dimensional space has an isomorphic copy in Type
--   - encoding: a_J in V_1^{⊗n} ⊗ ⋯ ⊗ V_k^{⊗n} → blockObj, the same tensor with legs U^{(i)}_{j_i}; reason: inclusion and projection restrict each to the other, so the class and the nonvanishing are the same, and conciseness is stated in the space the source names
--   - encoding: give a B-decomposition of length at most the product → each nonzero a_J lies in B and is ≤ t^{⊗n}; t^{⊗n} ≤ the sum over nonzero a_J; the number of nonzero a_J is at most the product; reason: this is the definition of a B-decomposition (p.13), spelled out
--   - encoding: t^{⊗n} with legs V_i^{⊗n} → kronPowPi X n, defined by the coordinate formula in chosen bases; reason: the indexed legs carry the 𝔖_n action, and the tensor does not depend on the bases
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), Lemma 3.4, pp.22–23

import Mathlib
import Definitions.Def_mme_tensor_quotient
import Definitions.Def_AsymSpecConn_tensorPreorder
import Definitions.Def_AsymSpecConn_flatRank
import Definitions.Def_AsymSpecConn_irreducibleSet
import Definitions.Def_AsymSpecConn_permRep
import Definitions.Def_AsymSpecConn_kronPowPi
import Definitions.Def_AsymSpecConn_blockObj

set_option autoImplicit false

open scoped TensorProduct

namespace AsymSpecConn

open scoped Classical in
/-- **Lemma 3.4** (pp.22–23 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)): "Let t ∈ V1 ⊗ ⋯ ⊗ Vk be nonzero and
let n ≥ 1. For every i ∈ [k] let 𝔖n act on Vi^{⊗n} by permuting the factors, let
Vi^{⊗n} = ⊕_{j=1}^{qi} Uj^{(i)} be a decomposition into irreducible 𝔖n-subrepresentations, and let
pj^{(i)} be the projection onto Uj^{(i)} along the other summands. Then the nonzero tensors
aj1,…,jk := (pj1^{(1)} ⊗ ⋯ ⊗ pjk^{(k)})t^{⊗n} give a B-decomposition of t^{⊗n} of length at most
Π_{i=1}^k (n + 1)^{(dim Vi)²}. Every nonzero aj1,…,jk is concise in Uj1^{(1)} ⊗ ⋯ ⊗ Ujk^{(k)}."

**Formalization Note** `t^{⊗n}` is `kronPowPi X n` (legs `V_i^{⊗n}`). `a J` is `blockObj`, the
tensor `a_{J}` viewed in `U^{(1)}_{J 1} ⊗ ⋯ ⊗ U^{(k)}_{J k}` (equivalent to the paper's `a_J` in
`V₁^{⊗n} ⊗ ⋯ ⊗ V_k^{⊗n}`, so it has the same class and the same nonvanishing). "Give a
B-decomposition" is spelled out: every nonzero `a_J` is in `B` and `a_J ≤ t^{⊗n}`, and
`t^{⊗n} ≤ ⊕_{J : a_J ≠ 0} a_J`; the length is the number of nonzero `a_J`. -/
theorem lemma_3_4 {k : ℕ} (hk : 2 ≤ k) (X : MME.TensorObj ℂ k) (hX : X.t ≠ 0) (n : ℕ)
    (hn : 1 ≤ n) (ι : Fin k → Type) [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)]
    (U : ∀ i, ι i → Subrepresentation (permRep ℂ (X.V i) n))
    (hU : ∀ i, DirectSum.IsInternal (fun j => (U i j).toSubmodule))
    (hirr : ∀ i j, (U i j).toRepresentation.IsIrreducible) :
    let a := blockObj (kronPowPi X n) (fun i j => (U i j).toSubmodule) hU
    let nz := Finset.univ.filter (fun J => (a J).t ≠ 0)
    (∀ J ∈ nz, MME.TensorQ.toQ (a J) ∈ jointlyIrreducibleSet hk) ∧
    (∀ J ∈ nz, (tensorPreorder ℂ hk).le (MME.TensorQ.toQ (a J))
      (MME.TensorQ.toQ (kronPowPi X n))) ∧
    (tensorPreorder ℂ hk).le (MME.TensorQ.toQ (kronPowPi X n))
      (∑ J ∈ nz, MME.TensorQ.toQ (a J)) ∧
    nz.card ≤ ∏ i, (n + 1) ^ (Module.finrank ℂ (X.V i) ^ 2) ∧
    (∀ J ∈ nz, IsConcise hk (a J)) := by sorry

end AsymSpecConn
