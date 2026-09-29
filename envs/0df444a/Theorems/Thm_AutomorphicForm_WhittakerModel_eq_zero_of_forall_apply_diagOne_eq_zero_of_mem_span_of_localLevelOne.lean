-- Prove2me | Theorems.Thm_AutomorphicForm_WhittakerModel_eq_zero_of_forall_apply_diagOne_eq_zero_of_mem_span_of_localLevelOne
-- name    : AutomorphicForm.WhittakerModel.eq_zero_of_forall_apply_diagOne_eq_zero_of_mem_span_of_localLevelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/d4455ee4-ee01-534c-b03c-e6c6e3d00448
-- title:
--   Kirillov injectivity for a Whittaker span at level K₁(N)
-- statement:
--   Let $p$ be a height-one prime of the ring of integers of $\mathbb Q$, let $N$ be a non-zero ideal of that ring, and let $w_2 \colon \mathrm{GL}_2(\mathbb Q_p) \to \mathbb C$ be a function on the general linear group of the completion at $p$ subject to four hypotheses. First, the Whittaker transformation law $w_2(u(x)g) = \psi_{\mathbb Q,p}(x)\, w_2(g)$ for all $x \in \mathbb Q_p$ and all $g$, where $u(x)$ is the unipotent matrix $\begin{pmatrix}1&x\\0&1\end{pmatrix}$ and $\psi_{\mathbb Q,p}$ is the local component at $p$ of the standard adelic additive character of $\mathbb Q$, namely `psiLocal`, obtained by composing `stdAddChar` with the additive embedding of $\mathbb Q_p$ into the adele ring placing an element at $p$. Second, right invariance $w_2(gk) = w_2(g)$ for all $k$ in [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178), the preimage under the local embedding $\mathrm{GL}_2(\mathbb Q_p) \to \mathrm{GL}_2(\mathbb A_{\mathbb Q}^{\mathrm{fin}})$ of the subgroup of adelic matrices $g$ such that both $g$ and $g^{-1}$ satisfy the level-one congruence condition `IsLevelOneMatrix` for $N$. Third, $w_2 \neq 0$. Fourth, a cyclicity condition: writing $S$ for the $\mathbb C$-span of the right translates $g \mapsto w_2(gh)$, every non-zero $w \in S$ has $w_2$ in the span of its own right translates. Fifth, admissibility: for every open subgroup $U$ there is a finite set $B$ of functions such that every $w \in S$ which is right $U$-invariant lies in the span of $B$. The conclusion is that any $w \in S$ with $w(\mathrm{diag}(y,1)) = 0$ for all $y \in \mathbb Q_p^{\times}$ is identically zero.
--
--   This is the injectivity of the Kirillov map: a vector in an irreducible admissible $\psi$-generic representation of $\mathrm{GL}_2(\mathbb Q_p)$ is determined by the restriction of its Whittaker function to the torus $\mathrm{diag}(y,1)$. It is stated here in the span-of-translates frame with the level-one congruence subgroup attached to $N$ providing smoothness, and is used in the Rankin–Selberg and Hecke-eigenvalue arguments, in particular by [`LanglandsTunnell.RankinSelberg.eq_zero_of_forall_integral_kirillov_pairing_eq_zero`](thm.html#LanglandsTunnell.RankinSelberg.eq_zero_of_forall_integral_kirillov_pairing_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WhittakerModel_eq_zero_of_forall_apply_diagOne_eq_zero_of_mem_span_of_localLevelOne.lean

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

theorem AutomorphicForm.WhittakerModel.eq_zero_of_forall_apply_diagOne_eq_zero_of_mem_span_of_localLevelOne
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
            w ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) :
    ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      (∀ y : (p.adicCompletion ℚ)ˣ, w (diagOne y) = 0) → w = 0 := by sorry
