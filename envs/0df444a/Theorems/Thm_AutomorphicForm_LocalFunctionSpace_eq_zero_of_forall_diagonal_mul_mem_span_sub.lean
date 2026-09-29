-- Prove2me | Theorems.Thm_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_diagonal_mul_mem_span_sub
-- name    : AutomorphicForm.LocalFunctionSpace.eq_zero_of_forall_diagonal_mul_mem_span_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/9d038c7f-f1ac-5ebe-8769-be4e269fa264
-- title:
--   Vanishing of a Whittaker function with trivial Kirillov image
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb{Q}$, write $F = \mathbb{Q}_p$ for the associated adic completion of $\mathbb{Q}$, and let $\psi =$ [`NumberField.StandardAddChar.psiV p`](def/NumberField_StandardGlobalAddCharRat.html#L224) be the additive character of $F$ obtained by transporting the standard additive character of $\mathbb{Q}_p$ along the identification of the completion with $\mathbb{Q}_p$. For $x \in F$ let $n(x) =$ [`AutomorphicForm.unipotentGL2 x`](def/AutomorphicForm_ConstantTerm.html#L17) be the element of $\mathrm{GL}_2(F)$ with matrix $\begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix}$. Let $S$ be a $\mathbb{C}$-submodule of the space of all functions $\mathrm{GL}_2(F) \to \mathbb{C}$, each member $U$ of which is smooth in the sense that there is an open subgroup $K \le \mathrm{GL}_2(F)$ with $U(gk) = U(g)$ for all $k \in K$ and all $g$. Let $W : \mathrm{GL}_2(F) \to \mathbb{C}$ satisfy $W(n(x)g) = \psi(x)W(g)$ for all $x \in F$ and $g \in \mathrm{GL}_2(F)$. Let $D \subseteq (\mathrm{GL}_2(F) \to \mathbb{C})$ be the $\mathbb{C}$-span of the functions $g \mapsto U(g\,n(x)) - \psi(x)U(g)$ with $U \in S$ and $x \in F$. Assume that for every $t \in \mathrm{GL}_2(F)$ whose off-diagonal matrix entries $t_{01}$, $t_{10}$ vanish and whose entry $t_{11}$ equals $1$, the right translate $g \mapsto W(gt)$ lies in $D$. Then $W = 0$. In particular $W$ is not assumed to lie in $S$, and no irreducibility, admissibility or translation-invariance of $S$ is assumed.
--
--   This is the injectivity step of the Kirillov-model description of a function satisfying the $\psi$-Whittaker law on the left: the hypothesis says that the Kirillov function $a \mapsto (g \mapsto W(g\,\mathrm{diag}(a,1)))$ of $W$ vanishes identically modulo the $\psi$-twisted unipotent defects of $S$, and the conclusion is that $W$ itself vanishes. It is used in the proof of [`AutomorphicForm.LocalFunctionSpace.mem_span_sub_of_apply_one_eq_zero_of_irreducible_of_admissible`](thm.html#AutomorphicForm.LocalFunctionSpace.mem_span_sub_of_apply_one_eq_zero_of_irreducible_of_admissible).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_diagonal_mul_mem_span_sub.lean

import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.LocalFunctionSpace.eq_zero_of_forall_diagonal_mul_mem_span_sub
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (S : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))
    (hsm : ∀ U ∈ S, ∃ K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ K, (fun g => U (g * k)) = U)
    (W : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hpsi : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W (AutomorphicForm.unipotentGL2 x * g) = NumberField.StandardAddChar.psiV p x * W g)
    (hD : ∀ t : GL (Fin 2) (p.adicCompletion ℚ),
      (t : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 0 1 = 0 →
      (t : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 0 = 0 →
      (t : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) 1 1 = 1 →
      (fun g => W (g * t)) ∈ Submodule.span ℂ
        {V : GL (Fin 2) (p.adicCompletion ℚ) → ℂ | ∃ U ∈ S, ∃ x : p.adicCompletion ℚ,
          V = (fun g => U (g * AutomorphicForm.unipotentGL2 x)) - NumberField.StandardAddChar.psiV p x • U}) :
    W = 0 := by sorry
