-- Prove2me | Theorems.Thm_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary
-- name    : ClassFunction.exists_one_eq_sum_zsmul_induced_one_of_hyperelementary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/7f73aeb1-1311-56d1-8c15-dfd3c0f50341
-- title:
--   Solomon's induction theorem for the trivial character
-- statement:
--   Let $G$ be a finite group (a type with a group structure and a `Fintype` instance). The assertion is that there exist a natural number $k$, a family of subgroups $H_0,\dots,H_{k-1}$ of $G$ indexed by `Fin k`, and integers $a_0,\dots,a_{k-1}$, with the following two properties. First, each $H_i$ is hyperelementary in the explicitly spelled-out sense: there is a prime $q$ and a subgroup $C \le H_i$ such that $C$ is cyclic, $\operatorname{Nat.card} C$ is coprime to $q$, $C$ is stable under conjugation by elements of $H_i$ (for all $h \in H_i$ and $c \in C$, $hch^{-1} \in C$), and every $h \in H_i$ satisfies $h^{q^n} \in C$ for some $n \in \mathbb{N}$. Second, for every $g \in G$ one has the identity in $\mathbb{Q}$ $$1 = \sum_{i} a_i \cdot \operatorname{induced}(H_i, \mathbf{1})(g),$$ where, by the definition of [`ClassFunction.induced`](def/ClassFunction_Induced.html#L13), $\operatorname{induced}(H, \varphi)(g) = (\operatorname{Nat.card} H)^{-1} \sum_{x \in G} \varphi(x^{-1} g x)$ summed over those $x$ with $x^{-1} g x \in H$, so that for the constant function $\varphi = 1$ this is $\#\{x \in G : x^{-1} g x \in H\} / |H|$, the number of cosets in $G/H$ fixed by $g$. The integers $a_i$ enter the sum through their image in $\mathbb{Q}$, multiplied by the value of the induced function.
--
--   This is Solomon's induction theorem: the trivial character of a finite group is an integral linear combination of the permutation characters of $G$ on coset spaces of hyperelementary subgroups, with hyperelementarity expressed elementwise rather than through a semidirect product decomposition. It is the first step of the Solomon–Dress route to Brauer's induction theorem, and is used here by [`BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter`](thm.html#BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter), which multiplies the identity by an arbitrary character and applies the projection formula.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary.lean

import Mathlib
import Definitions.Def_ClassFunction_Induced

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ClassFunction.exists_one_eq_sum_zsmul_induced_one_of_hyperelementary
    {G : Type} [Group G] [Fintype G] :
    ∃ (k : ℕ) (H : Fin k → Subgroup G) (a : Fin k → ℤ),
      (∀ i, ∃ q : ℕ, q.Prime ∧ ∃ C : Subgroup G, C ≤ H i ∧ IsCyclic C ∧ (Nat.card C).Coprime q ∧
        (∀ h ∈ H i, ∀ c ∈ C, h * c * h⁻¹ ∈ C) ∧ (∀ h ∈ H i, ∃ n : ℕ, h ^ q ^ n ∈ C)) ∧
      ∀ g : G, (1 : ℚ) = ∑ i, (a i : ℚ) * ClassFunction.induced (H i) (fun _ => (1 : ℚ)) g := by sorry
