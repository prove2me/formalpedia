-- Prove2me | Theorems.Thm_AutomorphicForm_WhittakerModel_forall_mem_span_smooth_and_law_and_central_and_growth_and_shellRecurrence
-- name    : AutomorphicForm.WhittakerModel.forall_mem_span_smooth_and_law_and_central_and_growth_and_shellRecurrence
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/1165dda7-ebec-5f9a-b2b3-09a57c6ab689
-- title:
--   Translates of a Whittaker vector: smoothness, growth, shell recurrence
-- statement:
--   Fix a height-one prime $p$ of $\mathcal{O}_{\mathbb{Q}}$, a homomorphism $\theta_0 \colon (\mathbb{Q}_p)^{\times} \to \mathbb{C}^{\times}$ from the units of the completion $K_p =$ `p.adicCompletion ℚ`, and a nonzero ideal $N$ of $\mathcal{O}_{\mathbb{Q}}$. Let $w_{2}\colon \mathrm{GL}_2(K_p) \to \mathbb{C}$ satisfy: the Whittaker law $w_2(n(x)g) = \psi_p(x)\,w_2(g)$ for the unipotent $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ and the local component $\psi_p$ at $p$ of the standard adelic additive character; right invariance under [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) at level $N$, the pullback along the local embedding $\mathrm{GL}_2(K_p) \to \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}})$ of the finite-adelic level-one subgroup of $N$; $w_2 \neq 0$; the condition that every nonzero element $w$ of the span $V = \mathrm{span}_{\mathbb{C}}\{g \mapsto w_2(gh)\}$ of right translates has $w_2$ in the span of its own right translates; admissibility, i.e. for every open subgroup $U$ there is a finite set $B$ of functions such that every $U$-right-invariant element of $V$ lies in $\mathrm{span}_{\mathbb{C}} B$; and the central character law $w_2(z \cdot g) = \theta_0(z) w_2(g)$ for scalar matrices. Let $\varpi$ be an element of the valuation ring with nonzero image and valuation $\exp(-1)$, i.e. a uniformiser, and write $a(m) = \mathrm{diag}(\varpi^{m},1)$. Then every $w \in V$ satisfies: (1) $w$ is right invariant under some open subgroup of $\mathrm{GL}_2(K_p)$; (2) the same Whittaker law with $\psi_p$; (3) the same central character $\theta_0$; (4) there are reals $C, A'$ with $\lVert w(a(m)k)\rVert \le C\,(\mathrm{absNorm}\,p)^{A'm}$ for all integers $m \ge 0$ and all $k$ in [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) at level $\top$; and (5) there are an integer $N_1$, a polynomial $D \in \mathbb{C}[X]$ with $D(0) \neq 0$, and $M \in \mathbb{N}$ such that, for every such $k$, the shell values $w(a(m)k)$ vanish for $m < N_1$ and $\sum_{i=0}^{\deg D} D_i\, w(a(N_1 + m - i)k) = 0$ for all naturals $m \ge M$.
--
--   This is the statement that the whole span of right translates of a single smooth Whittaker vector again consists of smooth vectors with the same $\psi_p$-equivariance and central character, and that the associated shell sequences along the torus elements $\mathrm{diag}(\varpi^m,1)$ are uniformly polynomially bounded and satisfy one common linear recurrence with nonvanishing constant term — the finiteness properties of the Kirillov model. It supplies the local input for the Rankin–Selberg zeta integral and functional equation lemmas of the Langlands–Tunnell component, which cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WhittakerModel_forall_mem_span_smooth_and_law_and_central_and_growth_and_shellRecurrence.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_CubicInduction_IotaTorus
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField AutomorphicForm UnramifiedWhittaker
  LanglandsTunnell.TateLocal LanglandsTunnell.CubicInduction

theorem AutomorphicForm.WhittakerModel.forall_mem_span_smooth_and_law_and_central_and_growth_and_shellRecurrence
    (p : HeightOneSpectrum (𝓞 ℚ))
    (θ₀ : (p.adicCompletion ℚ)ˣ →* ℂˣ)
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
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w₂base g)
    {ϖ : p.adicCompletionIntegers ℚ}
    (hπ : algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) = WithZero.exp (-1 : ℤ))
    :
    ∀ w ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
      (∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
        ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), w (g * k) = w g) ∧
      (∀ (x : p.adicCompletion ℚ) (g : GL (Fin 2) (p.adicCompletion ℚ)), w (unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ p x * w g) ∧
      (∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        w (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((θ₀ z : ℂˣ) : ℂ) * w g) ∧
      (∃ (C A' : ℝ), ∀ (m : ℤ), 0 ≤ m → ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
        ‖w (diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k)‖ ≤ C * (Ideal.absNorm p.asIdeal : ℝ) ^ (A' * m)) ∧
      (∃ (N₁ : ℤ) (D : Polynomial ℂ) (M : ℕ), D.eval 0 ≠ 0 ∧
        ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p ⊤,
          (∀ m : ℤ, m < N₁ → w (diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ m * k) = 0) ∧
          (∀ m : ℕ, M ≤ m →
            ∑ i ∈ Finset.range (D.natDegree + 1), D.coeff i * w (diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) ϖ) hπ (N₁ + (m : ℤ) - (i : ℤ)) * k) = 0)) := by sorry
