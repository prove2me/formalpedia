-- Prove2me | Theorems.Thm_AutomorphicForm_WhittakerModel_exists_polynomial_forall_diagZ_mul_eq_zero_and_sum_coeff_mul_eq_zero_of_admissible
-- name    : AutomorphicForm.WhittakerModel.exists_polynomial_forall_diagZ_mul_eq_zero_and_sum_coeff_mul_eq_zero_of_admissible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/ea861cff-7496-540d-912e-41f20fcf2ef1
-- title:
--   Shell vanishing and recurrence for admissible Whittaker spaces
-- statement:
--   Let $p$ be a nonzero prime ideal of the ring of integers of $\mathbb{Q}$, write $\mathbb{Q}_p$ for the completion `p.adicCompletion ℚ`, and let $V$ be a $\mathbb{C}$-submodule of the space of all functions $GL_2(\mathbb{Q}_p) \to \mathbb{C}$ subject to four hypotheses: $V$ is stable under right translation, i.e. for $W \in V$ and $h \in GL_2(\mathbb{Q}_p)$ the function $g \mapsto W(gh)$ lies in $V$; every $W \in V$ satisfies the Whittaker transformation law $W(n(x)g) = \psi_p(x)\,W(g)$ for all $x \in \mathbb{Q}_p$ and $g$, where $n(x)$ is the unipotent matrix $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $\psi_p$ is [`NumberField.StandardAddChar.psiLocal ℚ p`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65), the standard adelic additive character of $\mathbb{Q}$ composed with the additive embedding of $\mathbb{Q}_p$ into the adele ring at the place $p$; every $W \in V$ is smooth, in the sense that some open subgroup $U \le GL_2(\mathbb{Q}_p)$ satisfies $W(gk) = W(g)$ for all $k \in U$ and all $g$; and $V$ is admissible, in the sense that for every open subgroup $U$ there is a finite set $B$ of functions $GL_2(\mathbb{Q}_p) \to \mathbb{C}$ such that every $W \in V$ invariant under right translation by $U$ lies in the $\mathbb{C}$-span of $B$. No irreducibility is assumed. Let further $\varpi$ be an element of the valuation ring of $\mathbb{Q}_p$ whose image in $\mathbb{Q}_p$ is nonzero and has valuation $\mathrm{exp}(-1)$, that is, a uniformiser. Then for every $W \in V$ there exist an integer $N_1$, a polynomial $D \in \mathbb{C}[X]$ with $D(0) \neq 0$, and a natural number $M$, such that for every $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤`](def/AdelicDock_LocalEmbedding.html#L178) — the preimage in $GL_2(\mathbb{Q}_p)$, under the homomorphism placing a local matrix at $p$ and the identity elsewhere, of the level-one subgroup `AdelicLevel.finiteLevelOne` of $GL_2$ of the finite adele ring at the unit ideal, consisting of the adelic matrices $g$ with both $g$ and $g^{-1}$ satisfying `IsLevelOneMatrix` — the following hold, with $d(m)$ denoting the diagonal matrix $\mathrm{diag}(\varpi^m, 1)$ in $GL_2(\mathbb{Q}_p)$: first, $W(d(m)k) = 0$ for every integer $m < N_1$; second, for every natural number $m \ge M$, $\sum_{i=0}^{\deg D} D_i\, W\bigl(d(N_1 + m - i)\,k\bigr) = 0$. The data $N_1$, $D$, $M$ are uniform in $k$.
--
--   This is the local statement that the Kirillov-type restriction of a smooth admissible Whittaker space to the shells $\mathrm{diag}(\varpi^m,1)\,K_p$ vanishes for $m$ sufficiently negative and satisfies a fixed linear recurrence (with characteristic polynomial $D$, normalised by $D(0) \neq 0$) for $m$ sufficiently large, uniformly over the level-one compact subgroup. It is used downstream to derive polynomial growth bounds for such Whittaker functions, to produce spanning sets of functions with these shell properties, and in the construction of the local Rankin–Selberg integrals in the Langlands–Tunnell part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WhittakerModel_exists_polynomial_forall_diagZ_mul_eq_zero_and_sum_coeff_mul_eq_zero_of_admissible.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker LanglandsTunnell.TateLocal NumberField.AdelicLevel

theorem AutomorphicForm.WhittakerModel.exists_polynomial_forall_diagZ_mul_eq_zero_and_sum_coeff_mul_eq_zero_of_admissible
    (p : HeightOneSpectrum (𝓞 ℚ))
    (V : Submodule ℂ (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))
    (hstab : ∀ W ∈ V, ∀ h : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * h)) ∈ V)
    (hlaw : ∀ W ∈ V, ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * W g)
    (hsm : ∀ W ∈ V, ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g)
    (hadm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), ∀ W ∈ V, (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) →
        W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ)) :
    ∀ W ∈ V, ∃ (N₁ : ℤ) (D : Polynomial ℂ) (M : ℕ), D.eval 0 ≠ 0 ∧
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
        (∀ m : ℤ, m < N₁ →
          W (diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k) = 0) ∧
        (∀ m : ℕ, M ≤ m →
          ∑ i ∈ Finset.range (D.natDegree + 1),
            D.coeff i *
              W (diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ (N₁ + (m : ℤ) - (i : ℤ)) * k) = 0) := by sorry
