-- Prove2me | Theorems.Thm_AutomorphicForm_WhittakerModel_exists_forall_diagZ_mul_eq_zero_and_norm_le_mul_zpow_of_admissible
-- name    : AutomorphicForm.WhittakerModel.exists_forall_diagZ_mul_eq_zero_and_norm_le_mul_zpow_of_admissible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/0d25f81c-dff5-59ae-924a-ceea77c094ad
-- title:
--   Gauge bound for torus values of admissible Whittaker functions
-- statement:
--   Let $p$ be a height-one prime of $\mathcal O_{\mathbb Q}$, write $\mathbb Q_p$ for the completion $p.\mathrm{adicCompletion}\ \mathbb Q$, and let $V$ be a $\mathbb C$-submodule of the space of all functions $GL_2(\mathbb Q_p)\to\mathbb C$ subject to four hypotheses: (i) $V$ is stable under right translation, i.e. $g\mapsto W(gh)$ lies in $V$ for all $W\in V$ and $h\in GL_2(\mathbb Q_p)$; (ii) every $W\in V$ satisfies the Whittaker transformation law $W(\mathrm{unipotent}(x)\,g)=\psi_p(x)\,W(g)$, where $\mathrm{unipotent}(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $\psi_p=$ [`NumberField.StandardAddChar.psiLocal`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65) $\mathbb Q\,p$ is the additive character of $\mathbb Q_p$ obtained by composing the standard adelic character `stdAddChar` of $\mathbb Q$ with the additive map sending $x$ to the adele with component $x$ at $p$; (iii) smoothness: each $W\in V$ is fixed under right translation by some open subgroup; (iv) admissibility: for every open subgroup $U\le GL_2(\mathbb Q_p)$ there is a finite set $B$ of functions such that every $W\in V$ which is right $U$-invariant lies in the $\mathbb C$-span of $B$. Let $\varpi$ be an element of the valuation ring of $\mathbb Q_p$ whose image $\varpi\in\mathbb Q_p$ is nonzero and has valuation $\exp(-1)$, i.e. a uniformiser. Then for every $W\in V$ there are an integer $N_1$ and reals $C\ge 0$, $R>0$ such that for every $k$ in the subgroup [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) $\mathcal O_{\mathbb Q}\ \mathbb Q\ p\ \top$ — the preimage under the place-$p$ embedding `localEmbed` into $GL_2$ of the finite adeles of the subgroup `finiteLevelOne` at the unit ideal, consisting of those $g$ for which both $g$ and $g^{-1}$ satisfy the predicate `IsLevelOneMatrix` at level $\top$ — and for every $m\in\mathbb Z$, setting $a_m=\begin{pmatrix}\varpi^m&0\\0&1\end{pmatrix}$: one has $W(a_mk)=0$ whenever $m<N_1$, and $\|W(a_mk)\|\le C R^{m}$ for all $m$, with $N_1$, $C$, $R$ independent of $k$.
--
--   This is the gauge estimate for the Kirillov-type restriction of an admissible smooth Whittaker space on $GL_2(\mathbb Q_p)$: the values on the diagonal torus vanish far out in one direction and grow at most geometrically in the other, uniformly over the compact open subgroup at level one. Irreducibility of $V$ is not assumed; the bound feeds the convergence and majorisation arguments for local Rankin–Selberg integrals and the spanning statements for spaces of Whittaker functions that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WhittakerModel_exists_forall_diagZ_mul_eq_zero_and_norm_le_mul_zpow_of_admissible.lean

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

theorem AutomorphicForm.WhittakerModel.exists_forall_diagZ_mul_eq_zero_and_norm_le_mul_zpow_of_admissible
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
    ∀ W ∈ V, ∃ (N₁ : ℤ) (C R : ℝ), 0 ≤ C ∧ 0 < R ∧
      ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤, ∀ m : ℤ,
        (m < N₁ → W (diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k) = 0) ∧
        ‖W (diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤ C * R ^ m := by sorry
