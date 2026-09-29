-- Prove2me | Theorems.Thm_Coalgebra_exists_finiteDimensional_le_comul_mem_span
-- name    : Coalgebra.exists_finiteDimensional_le_comul_mem_span
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/1044caa0-ceaf-5f60-9987-523f40fa5ae3
-- title:
--   Local finiteness of coalgebras, relative form
-- statement:
--   Let $k$ be a field and let $C$ be a $k$-coalgebra (an additive commutative group with a $k$-module structure and a `Coalgebra k C` structure, so in particular with comultiplication $\mathrm{comul} : C \to C \otimes_k C$). Let $K$ be a $k$-submodule of $C$ which is stable under comultiplication in the following explicit sense: for every $x \in K$, $\mathrm{comul}(x)$ lies in the $k$-span of the set of tensors $t \in C \otimes_k C$ for which there exist $a \in K$ and $b \in K$ with $t = a \otimes b$. Let $x$ be an element of $C$ lying in $K$. The conclusion is that there exists a $k$-submodule $D$ of $C$ with $D \le K$, such that $D$ is finite-dimensional over $k$, such that $x \in D$, and such that $D$ is again stable under comultiplication in the same explicit sense: for every $y \in D$, $\mathrm{comul}(y)$ lies in the $k$-span of the tensors of the form $a \otimes b$ with $a \in D$ and $b \in D$.
--
--   This is the local finiteness of coalgebras over a field — the statement that every element lies in a finite-dimensional subcoalgebra, sometimes called the fundamental theorem of coalgebras — in a relative form in which the subcoalgebra is required to sit inside a prescribed comultiplication-stable subspace $K$ (the absolute form is the case $K = C$). It is used in the construction of finitely generated Hopf subalgebras: [`HopfAlgebra.exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset`](thm.html#HopfAlgebra.exists_fg_subalgebra_comul_mem_antipode_mem_of_finset_subset) appeals to it to find, inside a given stable subspace, a finite-dimensional piece containing a prescribed element.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Coalgebra_exists_finiteDimensional_le_comul_mem_span.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem Coalgebra.exists_finiteDimensional_le_comul_mem_span
    {k : Type u} [Field k] {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]
    (K : Submodule k C)
    (hK : ∀ x ∈ K, Coalgebra.comul (R := k) x ∈
      Submodule.span k {t : C ⊗[k] C | ∃ a ∈ K, ∃ b ∈ K, t = a ⊗ₜ[k] b})
    (x : C) (hx : x ∈ K) :
    ∃ D : Submodule k C, D ≤ K ∧ FiniteDimensional k ↥D ∧ x ∈ D ∧
      ∀ y ∈ D, Coalgebra.comul (R := k) y ∈
        Submodule.span k {t : C ⊗[k] C | ∃ a ∈ D, ∃ b ∈ D, t = a ⊗ₜ[k] b} := by sorry
