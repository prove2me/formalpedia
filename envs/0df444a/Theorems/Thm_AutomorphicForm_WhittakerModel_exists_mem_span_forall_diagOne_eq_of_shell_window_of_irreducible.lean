-- Prove2me | Theorems.Thm_AutomorphicForm_WhittakerModel_exists_mem_span_forall_diagOne_eq_of_shell_window_of_irreducible
-- name    : AutomorphicForm.WhittakerModel.exists_mem_span_forall_diagOne_eq_of_shell_window_of_irreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/83450aaf-ad34-5fa6-b4c9-de52ea91d675
-- title:
--   Kirillov model contains the compactly supported locally constant functions
-- statement:
--   Fix a height-one prime $p$ of the ring of integers of $\mathbb{Q}$ and write $\mathbb{Q}_p$ for the completion `p.adicCompletion ℚ`. Let $w_2 : \mathrm{GL}_2(\mathbb{Q}_p) \to \mathbb{C}$ satisfy the Whittaker transformation law $w_2(n(x)g) = \psi_p(x)\,w_2(g)$ for all $x \in \mathbb{Q}_p$ and $g$, where $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ is `unipotent x` and $\psi_p =$ [`NumberField.StandardAddChar.psiLocal ℚ p`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65) is the additive character obtained by composing the standard adelic character of $\mathbb{Q}$ with the additive embedding of $\mathbb{Q}_p$ into the adeles at $p$. Assume, for some $c \in \mathbb{N}$, that $w_2(gk) = w_2(g)$ for all $g$ and all $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ c)`](def/AdelicDock_LocalEmbedding.html#L178), the subgroup of those $k$ whose image under the embedding of $\mathrm{GL}_2(\mathbb{Q}_p)$ into $\mathrm{GL}_2$ of the finite adeles (placing $k$ at $p$ and the identity elsewhere) has both it and its inverse satisfying the predicate `IsLevelOneMatrix` for the ideal $p^c$. Assume further $w_2 \neq 0$ and that the span $V$ over $\mathbb{C}$ of the right translates $g \mapsto w_2(gh)$, $h \in \mathrm{GL}_2(\mathbb{Q}_p)$, is irreducible in the sense that every nonzero $w \in V$ has $w_2$ in the span of its own right translates $g \mapsto w(gh)$. Let $f : \mathbb{Q}_p^\times \to \mathbb{C}$, let $n_1, n_0 \in \mathbb{Z}$ and $m \in \mathbb{N}$, and suppose $f(y) = 0$ whenever $|y| > \exp(-n_1)$ or $|y| < \exp(-n_0)$, and $f(yu) = f(y)$ for all $y$ and all units $u$ with $|u| = 1$ and $|u - 1| \le \exp(-m)$. Then there is $w \in V$ with $w\big(\mathrm{diag}(y,1)\big) = f(y)$ for every $y \in \mathbb{Q}_p^\times$, where $\mathrm{diag}(y,1)$ is `diagOne y`.
--
--   This is the statement that the Kirillov model of an irreducible generic smooth representation of $\mathrm{GL}_2(\mathbb{Q}_p)$ contains every locally constant, compactly supported function on $\mathbb{Q}_p^\times$, with the function class spelled out concretely as a finite window of valuation shells together with invariance under a congruence subgroup of units. It feeds a variant of itself stated for the level-one congruence subgroup, and the Rankin–Selberg functional-equation results for Godement zeta integrals used in the Langlands–Tunnell part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WhittakerModel_exists_mem_span_forall_diagOne_eq_of_shell_window_of_irreducible.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker NumberField.AdelicLevel

theorem AutomorphicForm.WhittakerModel.exists_mem_span_forall_diagOne_eq_of_shell_window_of_irreducible
    (p : HeightOneSpectrum (𝓞 ℚ))

    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (c : ℕ)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ c), ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ
        (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          w₂base (g * h)),
      w ≠ 0 →
        w₂base ∈
          Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
            fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))

    (f : (p.adicCompletion ℚ)ˣ → ℂ) (n₁ n₀ : ℤ) (m : ℕ)
    (hf₀ : ∀ y : (p.adicCompletion ℚ)ˣ,
      WithZero.exp (-n₁) < Valued.v (y : p.adicCompletion ℚ) ∨ Valued.v (y : p.adicCompletion ℚ) < WithZero.exp (-n₀) →
        f y = 0)
    (hf₁ : ∀ y u : (p.adicCompletion ℚ)ˣ, Valued.v (u : p.adicCompletion ℚ) = 1 →
      Valued.v ((u : p.adicCompletion ℚ) - 1) ≤ WithZero.exp (-(m : ℤ)) → f (y * u) = f y) :
    ∃ w ∈ Submodule.span ℂ
        (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ y : (p.adicCompletion ℚ)ˣ, w (diagOne y) = f y := by sorry
