-- Prove2me | Theorems.Thm_AutomorphicForm_WhittakerModel_forall_mem_span_sub_unipotent_of_forall_diagOne_eq_zero_of_irreducible_of_admissible
-- name    : AutomorphicForm.WhittakerModel.forall_mem_span_sub_unipotent_of_forall_diagOne_eq_zero_of_irreducible_of_admissible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/f7d6f833-37a1-54ef-b6c2-988f41286ffb
-- title:
--   Cuspidal Whittaker space equals V(N)
-- statement:
--   Fix a height-one prime $p$ of the ring of integers of $\mathbb{Q}$ and a non-zero ideal $N$, and write $F = \mathbb{Q}_p$ for the completion of $\mathbb{Q}$ at $p$. Let $w_2 : GL_2(F) \to \mathbb{C}$ be a function satisfying: (i) the Whittaker transformation law $w_2\big(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\big)g) = \psi_p(x)\, w_2(g)$ for all $x \in F$, $g \in GL_2(F)$, where $\psi_p$ is `psiLocal`, the character obtained by composing the standard adelic additive character of $\mathbb{Q}$ with the embedding of $F$ into the adeles at the place $p$; (ii) right invariance $w_2(gk) = w_2(g)$ for all $k$ in `localLevelOne`, the preimage under the local embedding $GL_2(F) \to GL_2(\mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}})$ of the group of finite adelic matrices which, together with their inverses, are of level one for $N$; (iii) $w_2 \neq 0$. Let $V$ denote the $\mathbb{C}$-span of the right translates $g \mapsto w_2(gh)$, $h \in GL_2(F)$. Assume further: (iv) irreducibility in the form that for every non-zero $w \in V$, the function $w_2$ lies in the span of the right translates of $w$; (v) admissibility in the form that for every open subgroup $U \le GL_2(F)$ there is a finite set $B$ of functions $GL_2(F) \to \mathbb{C}$ such that every $U$-right-invariant element of $V$ lies in the span of $B$; (vi) cuspidality in the Kirillov sense: for every $v \in V$ there is an integer $N_0$ with $v(\mathrm{diag}(y,1)) = 0$ for every unit $y$ of $F$ with $\mathrm{v}(y) \le \exp(N_0)$. The conclusion is that every $W \in V$ lies in the $\mathbb{C}$-span of the set of functions of the form $g \mapsto W'\big(g\,\begin{smallmatrix}1&t\\0&1\end{smallmatrix}\big)\big) - W'(g)$ with $W' \in V$ and $t \in F$.
--
--   This is Jacquet's lemma in the Kirillov-model form: for an irreducible admissible generic representation whose Kirillov functions are supported away from $0$, one has $V = V(N)$, so that the Jacquet module $V/V(N)$ vanishes. It is used in the Rankin–Selberg part of the Langlands–Tunnell argument, where vanishing of the Jacquet module supplies the compact support needed for the local integrals and the functional equation of the Godement–Jacquet zeta integrals attached to cuspidal data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WhittakerModel_forall_mem_span_sub_unipotent_of_forall_diagOne_eq_zero_of_irreducible_of_admissible.lean

import Mathlib
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker NumberField.AdelicLevel

theorem AutomorphicForm.WhittakerModel.forall_mem_span_sub_unipotent_of_forall_diagOne_eq_zero_of_irreducible_of_admissible
    (p : HeightOneSpectrum (𝓞 ℚ))
    (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥)
    (w₂base : GL (Fin 2) (p.adicCompletion ℚ) → ℂ)
    (hw₂law : ∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w₂base g)
    (hw₂K : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p N, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w₂base (g * k) = w₂base g)
    (hw₂ne : w₂base ≠ 0)
    (hw₂irr : ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      w ≠ 0 → w₂base ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * h)))
    (hw₂adm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) →
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))

    (hcusp : ∀ v ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∃ N₀ : ℤ, ∀ y : (p.adicCompletion ℚ)ˣ, Valued.v (y : (p.adicCompletion ℚ)) ≤ WithZero.exp N₀ → v (diagOne y) = 0) :
    ∀ W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      W ∈ Submodule.span ℂ {D : GL (Fin 2) (p.adicCompletion ℚ) → ℂ | ∃ W' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        ∃ t : p.adicCompletion ℚ, D = fun g : GL (Fin 2) (p.adicCompletion ℚ) => W' (g * unipotent t) - W' g} := by sorry
