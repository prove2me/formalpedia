-- Prove2me | Theorems.Thm_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_mul_unipotent_eq
-- name    : AutomorphicForm.LocalFunctionSpace.eq_zero_of_forall_mul_unipotent_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/56596632-ec0c-5a48-ba71-7b245f505997
-- title:
--   Vanishing of unipotent-invariant local Whittaker functions
-- statement:
--   Let $\mathfrak p$ be a height-one prime of the ring of integers of $\mathbb Q$, and write $\mathbb Q_{\mathfrak p}$ for the completion `p.adicCompletion ℚ` of $\mathbb Q$ at $\mathfrak p$. Let $W : \mathrm{GL}_2(\mathbb Q_{\mathfrak p}) \to \mathbb C$ be any function, and for $x \in \mathbb Q_{\mathfrak p}$ let `unipotentGL2 x` denote the invertible matrix $\begin{pmatrix}1 & x\\ 0 & 1\end{pmatrix}$, with inverse $\begin{pmatrix}1 & -x\\ 0 & 1\end{pmatrix}$. Assume three conditions. First, $W$ transforms on the left by the standard additive character: $W(\mathrm{unipotentGL2}(x)\, g) = \psi_{\mathfrak p}(x)\, W(g)$ for all $x \in \mathbb Q_{\mathfrak p}$ and all $g$, where $\psi_{\mathfrak p}$ is [`NumberField.StandardAddChar.psiV p`](def/NumberField_StandardGlobalAddCharRat.html#L224), the additive character of $\mathbb Q_{\mathfrak p}$ obtained by composing the identification of $\mathbb Q_{\mathfrak p}$ with $\mathbb Q_p$ with the standard additive character `psiPadic` of $\mathbb Q_p$. Second, $W$ is smooth in the sense that there exists a subgroup $K \le \mathrm{GL}_2(\mathbb Q_{\mathfrak p})$ whose underlying set is open and such that $g \mapsto W(gk)$ equals $W$ for every $k \in K$. Third, $g \mapsto W(g\,\mathrm{unipotentGL2}(x))$ equals $W$ for every $x \in \mathbb Q_{\mathfrak p}$. Then $W$ is the zero function.
--
--   This is the local vanishing lemma for Whittaker-type functions at a finite place: a smooth function with the $\psi$-equivariance on the left cannot in addition be invariant under all right translations by upper unipotent matrices. It is used by [`AutomorphicForm.LocalFunctionSpace.eq_zero_of_forall_diagonal_mul_mem_span_sub`](thm.html#AutomorphicForm.LocalFunctionSpace.eq_zero_of_forall_diagonal_mul_mem_span_sub) in the treatment of constant terms of automorphic forms on $\mathrm{GL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalFunctionSpace_eq_zero_of_forall_mul_unipotent_eq.lean

import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AutomorphicForm.LocalFunctionSpace.eq_zero_of_forall_mul_unipotent_eq
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (W : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hpsi : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W (AutomorphicForm.unipotentGL2 x * g) = NumberField.StandardAddChar.psiV p x * W g)
    (hsm : ∃ K : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)),
      IsOpen (K : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ K, (fun g => W (g * k)) = W)
    (hfix : ∀ x : p.adicCompletion ℚ, (fun g => W (g * AutomorphicForm.unipotentGL2 x)) = W) :
    W = 0 := by sorry
