-- Prove2me | Theorems.Thm_AutomorphicForm_WhittakerModel_apply_mul_apply_eq_apply_mul_apply_of_forall_diagOne_eq_smul_of_transcendental
-- name    : AutomorphicForm.WhittakerModel.apply_mul_apply_eq_apply_mul_apply_of_forall_diagOne_eq_smul_of_transcendental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/e681a98f-b89b-58cc-b436-957b337aebea
-- title:
--   Multiplicity one for torus-eigenfunctionals on a Whittaker space
-- statement:
--   Fix a height-one prime $p$ of $\mathcal O_{\mathbb Q}$ and a non-zero ideal $N$ of $\mathcal O_{\mathbb Q}$, and write $F = \mathbb Q_p$ for the completion of $\mathbb Q$ at $p$. Let $w_2 : \mathrm{GL}_2(F) \to \mathbb C$ be a function such that (i) $w_2\bigl(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\bigr)g) = \psi_p(x)\,w_2(g)$ for all $x \in F$ and $g$, where $\psi_p$ is the component at $p$ of the standard additive character of the adeles of $\mathbb Q$, obtained by composing it with the inclusion of $F$ into the adele ring at the place $p$; (ii) $w_2(gk) = w_2(g)$ for all $k$ in the local level-$N$ subgroup at $p$, namely the preimage under the local embedding $\mathrm{GL}_2(F) \to \mathrm{GL}_2(\mathbb A_{\mathbb Q}^{\mathrm{fin}})$ of the group of finite-adelic matrices that, together with their inverses, satisfy the level-one congruence condition modulo $N$; (iii) $w_2 \neq 0$. Let $V$ be the $\mathbb C$-span of the right translates $g \mapsto w_2(gh)$, $h \in \mathrm{GL}_2(F)$. Assume further that $V$ is irreducible in the sense that for every non-zero $w \in V$ the function $w_2$ lies in the span of the right translates of $w$, and admissible in the sense that for every open subgroup $U \le \mathrm{GL}_2(F)$ there is a finite set $B$ of functions $\mathrm{GL}_2(F) \to \mathbb C$ such that every $w \in V$ which is right $U$-invariant lies in the $\mathbb C$-span of $B$. Let $\mathbb K$ be a field which is a $\mathbb C$-algebra, and let $c : F^{\times} \to \mathbb K$ be a function whose value at the distinguished uniformiser unit of $F$ (the image of a chosen uniformiser of $\mathcal O_{\mathbb Q}$ at $p$) is transcendental over $\mathbb C$. Let $L, L'$ be $\mathbb C$-linear maps from the space of all functions $\mathrm{GL}_2(F) \to \mathbb C$ to $\mathbb K$ satisfying, for every $a \in F^{\times}$ and every $w \in V$, $L(g \mapsto w(g\,\mathrm{diag}(a,1))) = c(a)\,L(w)$ and likewise for $L'$. Then $L(w)\,L'(w') = L(w')\,L'(w)$ for all $w, w' \in V$.
--
--   This is the local multiplicity-one assertion that the space of functionals on an irreducible admissible Whittaker model of $\mathrm{GL}_2(\mathbb Q_p)$ transforming under $\mathrm{diag}(a,1)$ by a fixed multiplier $c$ with $c(\varpi)$ transcendental over $\mathbb C$ is at most one-dimensional; it is stated in cross-multiplied form, with values in an arbitrary field containing $\mathbb C$, so that it applies to the pair of rational-function-valued local zeta integrals. It is used in the construction of the local functional equation for twisted Rankin–Selberg zeta integrals at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WhittakerModel_apply_mul_apply_eq_apply_mul_apply_of_forall_diagOne_eq_smul_of_transcendental.lean

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

theorem AutomorphicForm.WhittakerModel.apply_mul_apply_eq_apply_mul_apply_of_forall_diagOne_eq_smul_of_transcendental
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

    (𝕂 : Type) [Field 𝕂] [Algebra ℂ 𝕂]
    (c : (p.adicCompletion ℚ)ˣ → 𝕂) (hc : Transcendental ℂ (c (uniformizerUnit ℚ p)))

    (L L' : (GL (Fin 2) (p.adicCompletion ℚ) → ℂ) →ₗ[ℂ] 𝕂)
    (hL : ∀ (a : (p.adicCompletion ℚ)ˣ), ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      L (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * diagOne a)) = c a • L w)
    (hL' : ∀ (a : (p.adicCompletion ℚ)ˣ), ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      L' (fun g : GL (Fin 2) (p.adicCompletion ℚ) => w (g * diagOne a)) = c a • L' w) :
    ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      ∀ w' ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
        L w * L' w' = L w' * L' w := by sorry
