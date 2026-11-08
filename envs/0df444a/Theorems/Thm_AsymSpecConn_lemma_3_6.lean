-- Prove2me | Theorems.Thm_AsymSpecConn_lemma_3_6
-- name    : AsymSpecConn.lemma_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:39:00.462797+00:00
-- url     : https://prove2.me/theorems/3dbfeede-bc0c-4772-b228-93bf84087b30
-- title:
--   Lemma 3.6 — subspace translate averaging
-- statement:
--   Let $F$ be any field, let a finite group $G$ act irreducibly on a nonzero finite-dimensional $F$-vector space $V$, and let $U,W\subseteq V$ be subspaces. Then
--   $$\frac1{|G|}\sum_{g\in G}\dim(U\cap gW)\le\frac{\dim W}{\dim V}\dim U.$$
--
--   The average overlap of the translates of $W$ with $U$ is thus at most what generic subspaces would have.
--
--   **Formalization Note** Finite-dimensionality is the source's standing convention (p.12). Mathlib's irreducibility forces $V\ne0$.
--
--   Differences from the source: none.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…), Lemma 3.6, p.23

import Mathlib

set_option autoImplicit false

namespace AsymSpecConn

/-- **Lemma 3.6** (p.23 of Vrana and Zuiddam, *The asymptotic spectrum of tensors is connected*, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac…)): "Let F be any field, let a finite group G
act irreducibly on a nonzero F-vector space V, and let U, W ⊆ V be subspaces. Then
(1/|G|) Σ_{g∈G} dim(U ∩ gW) ≤ (dim W / dim V) dim U."

**Formalization Note** The action is a representation `ρ` with `ρ.IsIrreducible` (which forces
`V ≠ 0`); `gW` is `W.map (ρ g)`. `V` is finite-dimensional (standing convention, p.12). The
inequality is in `ℝ`. -/
theorem lemma_3_6 (F : Type*) [Field F] (G : Type*) [Group G] [Fintype G] (V : Type*)
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] (ρ : Representation F G V)
    (hρ : ρ.IsIrreducible) (U W : Submodule F V) :
    (1 / (Fintype.card G : ℝ)) * ∑ g : G, (Module.finrank F ↥(U ⊓ W.map (ρ g)) : ℝ) ≤
      (Module.finrank F W : ℝ) / (Module.finrank F V : ℝ) * (Module.finrank F U : ℝ) := by sorry

end AsymSpecConn
