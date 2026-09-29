-- Prove2me | Theorems.Thm_AutomorphicForm_WhittakerModel_exists_forall_diagOne_eq_zero_of_lt_modulus
-- name    : AutomorphicForm.WhittakerModel.exists_forall_diagOne_eq_zero_of_lt_modulus
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/2f25535f-3803-52bc-a38b-73bea27e7fc2
-- title:
--   Whittaker functions on GL₂(ℚₚ) vanish for large |y|
-- statement:
--   Let $p$ be a place of $\mathbb{Q}$ in the height-one spectrum of $\mathcal{O}_{\mathbb{Q}} = \mathbb{Z}$, and let $W$ be a complex-valued function on $\mathrm{GL}_2$ of the completion $\mathbb{Q}_p$ at $p$. Two hypotheses are imposed. First, the left Whittaker transformation law: for every $x \in \mathbb{Q}_p$ and every $g$, $W(\mathrm{unipotent}(x)\,g) = \psi_p(x)\,W(g)$, where $\mathrm{unipotent}(x)$ is the unit $!![1,x;0,1]$ of $\mathrm{GL}_2$ and $\psi_p =$ `psiLocal` $\mathbb{Q}\,p$ is the additive character of $\mathbb{Q}_p$ obtained by composing the standard adelic character `stdAddChar` of the adele ring of $\mathbb{Q}$ with the additive map placing an element of $\mathbb{Q}_p$ in the $p$-component of the finite part of the adeles. Second, smoothness in the weak form that some subgroup $U \le \mathrm{GL}_2(\mathbb{Q}_p)$ is open as a set and $W(gk) = W(g)$ for all $k \in U$ and all $g$. The conclusion asserts the existence of a real $c > 0$ such that for every unit $y$ of $\mathbb{Q}_p$ with $c < \mathrm{modulus}(y)$ — the module of $y$ as given by the distributive Haar character, i.e. $|y|_p$ — one has $W(\mathrm{diag}(y,1)) = 0$, where $\mathrm{diag}(y,1)$ denotes the element `diagOne y` of $\mathrm{GL}_2$ with diagonal entries $y$ and $1$.
--
--   This is the elementary half of the statement that a Whittaker (Kirillov) function is supported, on the diagonal torus, in a region $|y|_p \le c$ with $c$ depending on the individual function: no uniformity over a representation is claimed. It is used in the local analysis of Whittaker models, in the Rankin–Selberg computations of the Godement zeta integral and in the Fourier-analytic identification of Kirillov coefficients for cuspidal data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WhittakerModel_exists_forall_diagOne_eq_zero_of_lt_modulus.lean

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

theorem AutomorphicForm.WhittakerModel.exists_forall_diagOne_eq_zero_of_lt_modulus
    (p : HeightOneSpectrum (𝓞 ℚ))
    (W : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hlaw : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      W (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * W g)
    (hsm : ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : (p.adicCompletion ℚ)ˣ, c < modulus (y : p.adicCompletion ℚ) → W (diagOne y) = 0 := by sorry
