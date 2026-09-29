-- Prove2me | Theorems.Thm_AutomorphicForm_LocalFunctionSpace_exists_smul_eq_of_irreducible_of_admissible
-- name    : AutomorphicForm.LocalFunctionSpace.exists_smul_eq_of_irreducible_of_admissible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/299d0579-d934-56e6-b9a0-7fa343630dc4
-- title:
--   Schur's lemma for an irreducible admissible function space on GL₂
-- statement:
--   Let $p$ be a point of the height-one spectrum of the ring of integers of $\mathbb{Q}$, write $F = \mathbb{Q}_p$ for the associated adic completion, and let $G = GL_2(F)$. Let $S$ be a $\mathbb{C}$-submodule of the space of all functions $G \to \mathbb{C}$ subject to four hypotheses: $S$ is stable under right translation, i.e. for $W \in S$ and $k \in G$ the function $g \mapsto W(gk)$ lies in $S$; every $W \in S$ is smooth, in the sense that there is a subgroup $K \le G$ which is open as a subset of $G$ with $g \mapsto W(gk)$ equal to $W$ for all $k \in K$; $S$ is irreducible, in the sense that every $\mathbb{C}$-submodule $T \le S$ stable under right translation equals $\bot$ or $S$; and $S$ is admissible, in the sense that for every open subgroup $K \le G$, every submodule $T \le S$ all of whose members are invariant under right translation by each $k \in K$ is finite-dimensional over $\mathbb{C}$. Let $\Phi$ be a $\mathbb{C}$-linear endomorphism of the full function space which maps $S$ into $S$ and satisfies $\Phi(g \mapsto W(gk)) = (g \mapsto (\Phi W)(gk))$ for all $W \in S$ and $k \in G$. Then there is a single $c \in \mathbb{C}$ with $\Phi W = c \cdot W$ for every $W \in S$. The degenerate case $S = \bot$ is permitted, with $c = 0$.
--
--   This is Schur's lemma for irreducible admissible smooth representations of $GL_2$ over a $p$-adic field, in the concrete form in which the representation is realised as a right-translation-stable space of complex-valued functions on the group and the intertwining operator is an endomorphism of the ambient function space. It is used in the analysis of such local function spaces, in particular by [`AutomorphicForm.LocalFunctionSpace.mem_span_sub_of_apply_one_eq_zero_of_irreducible_of_admissible`](thm.html#AutomorphicForm.LocalFunctionSpace.mem_span_sub_of_apply_one_eq_zero_of_irreducible_of_admissible).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalFunctionSpace_exists_smul_eq_of_irreducible_of_admissible.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.LocalFunctionSpace.exists_smul_eq_of_irreducible_of_admissible
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (S : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))
    (hstab : ∀ W ∈ S, ∀ k : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * k)) ∈ S)
    (hsm : ∀ W ∈ S, ∃ K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ K, (fun g => W (g * k)) = W)
    (hirr : ∀ T : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), T ≤ S →
      (∀ W ∈ T, ∀ k : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * k)) ∈ T) → T = ⊥ ∨ T = S)
    (hadm : ∀ K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∀ T : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), T ≤ S →
        (∀ W ∈ T, ∀ k ∈ K, (fun g => W (g * k)) = W) → FiniteDimensional ℂ T)
    (Φ : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))
    (hΦS : ∀ W ∈ S, Φ W ∈ S)
    (hΦρ : ∀ W ∈ S, ∀ k : GL (Fin 2) (p.adicCompletion ℚ), Φ (fun g => W (g * k)) = fun g => Φ W (g * k)) :
    ∃ c : ℂ, ∀ W ∈ S, Φ W = c • W := by sorry
