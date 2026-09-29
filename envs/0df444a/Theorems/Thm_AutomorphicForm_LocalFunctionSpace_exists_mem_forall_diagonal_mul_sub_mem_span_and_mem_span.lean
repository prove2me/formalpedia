-- Prove2me | Theorems.Thm_AutomorphicForm_LocalFunctionSpace_exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span
-- name    : AutomorphicForm.LocalFunctionSpace.exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/3bfbb811-a397-56b8-826a-9a82bc0956da
-- title:
--   Cutting off a GL₂ function by a ball indicator modulo twisted defects
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$, write $F =$ `p.adicCompletion ℚ` for the completion at $p$ with its valuation $v$ taking values in $\mathrm{WithZero}(\mathrm{Multiplicative}\ \mathbb{Z})$, and let $S$ be a $\mathbb{C}$-submodule of the space of all functions $\mathrm{GL}_2(F) \to \mathbb{C}$ which is stable under right translation, i.e. $g \mapsto U(gk)$ lies in $S$ for every $U \in S$ and every $k \in \mathrm{GL}_2(F)$. Let $D \subseteq (\mathrm{GL}_2(F) \to \mathbb{C})$ be the $\mathbb{C}$-span of the set of functions of the form $\bigl(g \mapsto U(g\,n(x))\bigr) - \psi_p(x)\,U$ with $U \in S$ and $x \in F$, where $n(x)$ is the element of $\mathrm{GL}_2(F)$ with matrix $\begin{pmatrix}1 & x\\ 0 & 1\end{pmatrix}$ (inverse $n(-x)$) and $\psi_p$ is the additive character of $F$ obtained by transporting the standard additive character of $\mathbb{Q}_p$ along the identification of $F$ with $\mathbb{Q}_p$. Let $W \in S$ be right invariant under some open subgroup $K \le \mathrm{GL}_2(F)$, so that $g \mapsto W(gk)$ equals $W$ for all $k \in K$, and let $a_0 \in F$ and a unit $\delta$ of $\mathrm{WithZero}(\mathrm{Multiplicative}\ \mathbb{Z})$ be given. Then there exists $W' \in S$ with the following property for every $t \in \mathrm{GL}_2(F)$ whose matrix has both off-diagonal entries $0$ and lower-right entry $1$: if $v(t_{00} - a_0) < \delta$ then $\bigl(g \mapsto W'(gt)\bigr) - \bigl(g \mapsto W(gt)\bigr) \in D$, and otherwise $\bigl(g \mapsto W'(gt)\bigr) \in D$. The single $W'$ serves all such $t$ simultaneously.
--
--   This is the function-level step of Kirillov theory which makes the space $S$, read modulo the span of the $\psi_p$-twisted defects, closed under multiplication by the indicator function of the ball of radius $\delta$ about $a_0$ in the variable $a = t_{00}$: the diagonal translates of $W'$ realise the cut-off of those of $W$. It is used in the proof of [`AutomorphicForm.LocalFunctionSpace.mem_span_sub_of_apply_one_eq_zero_of_irreducible_of_admissible`](thm.html#AutomorphicForm.LocalFunctionSpace.mem_span_sub_of_apply_one_eq_zero_of_irreducible_of_admissible). No transformation law is imposed on the members of $S$ beyond right-translation stability, and the zero space with $W = 0$, $W' = 0$ is a degenerate instance.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalFunctionSpace_exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span.lean

import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.LocalFunctionSpace.exists_mem_forall_diagonal_mul_sub_mem_span_and_mem_span
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (S : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))
    (hstab : ∀ U ∈ S, ∀ k : GL (Fin 2) (p.adicCompletion ℚ), (fun g => U (g * k)) ∈ S)
    (W : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hW : W ∈ S)
    (hsmW : ∃ K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ K, (fun g => W (g * k)) = W)
    (a₀ : p.adicCompletion ℚ) (δ : (WithZero (Multiplicative ℤ))ˣ) :
    ∃ W' ∈ S, ∀ t : GL (Fin 2) (p.adicCompletion ℚ),
      (t : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1 = 0 →
      (t : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 = 0 →
      (t : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 = 1 →
      (Valued.v ((t : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0 - a₀) < (δ : WithZero (Multiplicative ℤ)) →
        (fun g => W' (g * t)) - (fun g => W (g * t)) ∈ Submodule.span ℂ
        {V : GL (Fin 2) (p.adicCompletion ℚ) → ℂ | ∃ U ∈ S, ∃ x : p.adicCompletion ℚ,
          V = (fun g => U (g * AutomorphicForm.unipotentGL2 x)) - NumberField.StandardAddChar.psiV p x • U}) ∧
      (¬ Valued.v ((t : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 0 - a₀) < (δ : WithZero (Multiplicative ℤ)) →
        (fun g => W' (g * t)) ∈ Submodule.span ℂ
        {V : GL (Fin 2) (p.adicCompletion ℚ) → ℂ | ∃ U ∈ S, ∃ x : p.adicCompletion ℚ,
          V = (fun g => U (g * AutomorphicForm.unipotentGL2 x)) - NumberField.StandardAddChar.psiV p x • U}) := by sorry
