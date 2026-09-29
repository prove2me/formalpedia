-- Prove2me | Theorems.Thm_AutomorphicForm_LocalFunctionSpace_mem_span_sub_of_apply_one_eq_zero_of_irreducible_of_admissible
-- name    : AutomorphicForm.LocalFunctionSpace.mem_span_sub_of_apply_one_eq_zero_of_irreducible_of_admissible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/317e8ed6-3ea7-56d3-b279-70b075eaede9
-- title:
--   Vanishing at 1 forces membership in the twisted unipotent span
-- statement:
--   Let $p$ be a point of the height-one spectrum of the ring of integers of $\mathbb{Q}$, write $F = \mathbb{Q}_p$ for the $p$-adic completion, and let $\psi =$ [`NumberField.StandardAddChar.psiV p`](def/NumberField_StandardGlobalAddCharRat.html#L224) be the standard additive character of $F$ (the standard $p$-adic character transported along the identification of the adic completion with $\mathbb{Q}_p$). For $x \in F$ let $n(x) =$ [`AutomorphicForm.unipotentGL2 x`](def/AutomorphicForm_ConstantTerm.html#L17) be the matrix $\begin{pmatrix}1 & x\\ 0 & 1\end{pmatrix}$, viewed as an element of $\mathrm{GL}_2(F)$. Let $S$ be a $\mathbb{C}$-submodule of the space of all functions $\mathrm{GL}_2(F) \to \mathbb{C}$ such that: (i) $S$ is stable under right translation, i.e. $g \mapsto W(gk)$ lies in $S$ for all $W \in S$ and $k \in \mathrm{GL}_2(F)$; (ii) every $W \in S$ is smooth, i.e. fixed by right translation by some open subgroup $K \le \mathrm{GL}_2(F)$; (iii) every $W \in S$ satisfies $W(n(x)g) = \psi(x)\,W(g)$ for all $x \in F$, $g \in \mathrm{GL}_2(F)$; (iv) $S$ is irreducible, in the sense that every right-translation-stable submodule $T \le S$ equals $\bot$ or $S$; and (v) $S$ is admissible, in the sense that for every open subgroup $K$, every submodule $T \le S$ all of whose members are right $K$-invariant is finite-dimensional over $\mathbb{C}$. Then every $W \in S$ with $W(1) = 0$ lies in the $\mathbb{C}$-span of the set of functions of the form $g \mapsto U(g\,n(x)) - \psi(x)\,U(g)$ with $U \in S$ and $x \in F$.
--
--   This is the local uniqueness statement underlying multiplicity one for Whittaker functionals: modulo the span of the $\psi$-twisted unipotent defects, a space $S$ as above is detected by evaluation at the identity, so its space of $\psi$-twisted unipotent coinvariants is at most one-dimensional (the case $S = 0$ being allowed). It is used to derive the vanishing criterion for members of $S$ with vanishing diagonal values, the multiplicity-one behaviour of the local spaces attached to cuspidal constituents, and the construction of Whittaker vectors in the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalFunctionSpace_mem_span_sub_of_apply_one_eq_zero_of_irreducible_of_admissible.lean

import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.LocalFunctionSpace.mem_span_sub_of_apply_one_eq_zero_of_irreducible_of_admissible
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (S : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))
    (hstab : ∀ W ∈ S, ∀ k : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * k)) ∈ S)
    (hsm : ∀ W ∈ S, ∃ K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
        IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ K, (fun g => W (g * k)) = W)
    (hpsi : ∀ W ∈ S, ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        W (AutomorphicForm.unipotentGL2 x * g) = NumberField.StandardAddChar.psiV p x * W g)
    (hirr : ∀ T : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), T ≤ S →
        (∀ W ∈ T, ∀ k : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * k)) ∈ T) →
        T = ⊥ ∨ T = S)
    (hadm : ∀ K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
        IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
        ∀ T : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), T ≤ S →
          (∀ W ∈ T, ∀ k ∈ K, (fun g => W (g * k)) = W) → FiniteDimensional ℂ T) :
    ∀ W ∈ S, W 1 = 0 → W ∈ Submodule.span ℂ
      {V : GL (Fin 2) (p.adicCompletion ℚ) → ℂ | ∃ U ∈ S, ∃ x : p.adicCompletion ℚ,
        V = (fun g => U (g * AutomorphicForm.unipotentGL2 x)) - NumberField.StandardAddChar.psiV p x • U} := by sorry
