-- Prove2me | Theorems.Thm_AsymSpecConn_lemma_3_3
-- name    : AsymSpecConn.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:39:56.338797+00:00
-- url     : https://prove2.me/theorems/448b1b70-7870-434d-ae4d-09b36a88d35f
-- title:
--   Lemma 3.3 — polynomial count of irreducible summands of $V^{\otimes n}$
-- statement:
--   Let $V$ be a complex vector space of dimension $d\ge1$, let $n\ge1$, and let $\mathfrak S_n$ act on $V^{\otimes n}$ by permuting the factors. Then every decomposition of $V^{\otimes n}$ into irreducible $\mathfrak S_n$-subrepresentations has at most $(n+1)^{d^2}$ summands.
--
--   The bound is polynomial in $n$, which is what the method of types needs.
--
--   **Formalization Note** A decomposition is a finite family of subrepresentations whose underlying subspaces form an internal direct sum, each irreducible as a representation of $\mathfrak S_n$.
--
--   Differences from the source: none.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), Lemma 3.3, p.22

import Mathlib
import Definitions.Def_AsymSpecConn_permRep

set_option autoImplicit false

open scoped TensorProduct

namespace AsymSpecConn

/-- **Lemma 3.3** (p.22 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)): "Let V be a complex vector space of
dimension d ≥ 1, let n ≥ 1, and let 𝔖n act on V^{⊗n} by permuting the factors. Then every
decomposition of V^{⊗n} into irreducible 𝔖n-subrepresentations has at most (n + 1)^{d²}
summands."

**Formalization Note** A decomposition is a finite family `U` of subrepresentations of
`permRep ℂ V n` whose underlying subspaces form an internal direct sum (`DirectSum.IsInternal`),
each irreducible as a representation of `𝔖_n = Equiv.Perm (Fin n)`. `V` is finite-dimensional
(standing convention, p.12). -/
theorem lemma_3_3 (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (hd : 1 ≤ Module.finrank ℂ V) (n : ℕ) (hn : 1 ≤ n) (ι : Type*) [Fintype ι] [DecidableEq ι]
    (U : ι → Subrepresentation (permRep ℂ V n))
    (hU : DirectSum.IsInternal (fun j => (U j).toSubmodule))
    (hirr : ∀ j, (U j).toRepresentation.IsIrreducible) :
    Fintype.card ι ≤ (n + 1) ^ (Module.finrank ℂ V ^ 2) := by sorry

end AsymSpecConn
