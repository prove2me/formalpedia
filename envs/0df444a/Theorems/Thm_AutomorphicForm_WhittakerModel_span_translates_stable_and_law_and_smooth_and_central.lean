-- Prove2me | Theorems.Thm_AutomorphicForm_WhittakerModel_span_translates_stable_and_law_and_smooth_and_central
-- name    : AutomorphicForm.WhittakerModel.span_translates_stable_and_law_and_smooth_and_central
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/331d0a29-1fef-504c-9d2c-85de6ea43ac6
-- title:
--   Span of right translates of a local Whittaker function
-- statement:
--   Fix a nonzero prime $p$ of the ring of integers of $\mathbb{Q}$ and write $\mathbb{Q}_p$ for the completion $p$.adicCompletion $\mathbb{Q}$. Let $w_0 =$ `w₂base` be an arbitrary function $GL_2(\mathbb{Q}_p) \to \mathbb{C}$ (no continuity or measurability assumed) subject to three hypotheses: (i) $w_0(n(x)g) = \psi_p(x)\,w_0(g)$ for all $x \in \mathbb{Q}_p$ and $g \in GL_2(\mathbb{Q}_p)$, where $n(x)$ is the unipotent matrix $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $\psi_p$ is `psiLocal`, the additive character obtained by composing the standard adelic character of $\mathbb{Q}$ with the embedding of $\mathbb{Q}_p$ into the adeles placing an element at $p$ and zero elsewhere; (ii) for some $c \in \mathbb{N}$, right invariance $w_0(gk) = w_0(g)$ for all $k$ in `localLevelOne` at level $p^c$, the subgroup of $GL_2(\mathbb{Q}_p)$ pulled back along the local embedding at $p$ from the adelic level-$p^c$ subgroup; (iii) $w_0(\mathrm{scalar}(z)g) = \omega(z)\,w_0(g)$ for a homomorphism $\omega : \mathbb{Q}_p^\times \to \mathbb{C}^\times$. Let $V$ be the $\mathbb{C}$-span of the set of right translates $g \mapsto w_0(gh)$, $h \in GL_2(\mathbb{Q}_p)$. Then every $W \in V$ satisfies: $g \mapsto W(gh)$ again lies in $V$ for every $h$; $W(n(x)g) = \psi_p(x)W(g)$; there exists an open subgroup $U \le GL_2(\mathbb{Q}_p)$ with $W(gk) = W(g)$ for all $k \in U$ and all $g$; and $W(\mathrm{scalar}(z)g) = \omega(z)W(g)$.
--
--   This records that the four defining features of a local Whittaker vector — stability under right translation, the $\psi_p$-transformation law along the unipotent subgroup, smoothness, and the central character — pass from a single generator to every vector of the space it spans, with no irreducibility or cyclicity assumption. It is used in the Rankin–Selberg part of the Langlands–Tunnell argument, in the construction of integrable Godement zeta integrals of shifted Whittaker functions and in the computation of translated Kirillov pairings for cuspidal data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WhittakerModel_span_translates_stable_and_law_and_smooth_and_central.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker NumberField.AdelicLevel

theorem
  AutomorphicForm.WhittakerModel.span_translates_stable_and_law_and_smooth_and_central
    (p : HeightOneSpectrum (𝓞 ℚ))
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (c : ℕ)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ c), ∀ g : GL (Fin 2) (p.adicCompletion ℚ),
      w₂base (g * k) = w₂base g)
    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * w₂base g) :
    (∀ W ∈ Submodule.span ℂ
        (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ h : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * h)) ∈ Submodule.span ℂ
        (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h))) ∧
    (∀ W ∈ Submodule.span ℂ
        (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        W (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * W g) ∧
    (∀ W ∈ Submodule.span ℂ
        (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
        ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) ∧
    (∀ W ∈ Submodule.span ℂ
        (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
          fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        W (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * W g) := by sorry
