-- Prove2me | Theorems.Thm_AutomorphicForm_WhittakerModel_exists_torusZeta_dual_eq_stdRootNumberAt_mul_stdRootNumberAt_mul_of_admissible_of_le_of_norm_eq_one
-- name    : AutomorphicForm.WhittakerModel.exists_torusZeta_dual_eq_stdRootNumberAt_mul_stdRootNumberAt_mul_of_admissible_of_le_of_norm_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/aeeb5bd6-9f5a-5aaa-9886-f6b2318a8ec0
-- title:
--   Deep twist functional equation for GL₂ Whittaker torus integrals
-- statement:
--   Let $p$ be a nonzero prime ideal of the ring of integers of $\mathbb{Q}$, and let $w_{2}^{\mathrm{base}} \colon \mathrm{GL}_2(\mathbb{Q}_p) \to \mathbb{C}$ satisfy $w_{2}^{\mathrm{base}}\big(\binom{1\ x}{0\ 1}g\big) = \psi_p(x)\,w_{2}^{\mathrm{base}}(g)$, where $\psi_p$ is the local component [`NumberField.StandardAddChar.psiLocal`](def/LanglandsTunnell_StandardLocalConstantsAt.html#L65) of the standard adelic additive character at $p$; let $c \in \mathbb{N}$ be such that $w_{2}^{\mathrm{base}}$ is invariant under right translation by the group [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) of level $p^{c}$, i.e. the pullback along the embedding of $\mathrm{GL}_2(\mathbb{Q}_p)$ into $\mathrm{GL}_2$ of the finite adeles of the finite level-one subgroup of level $p^{c}$; assume $w_{2}^{\mathrm{base}} \neq 0$; that the $\mathbb{C}$-span $V$ of the right translates $g \mapsto w_{2}^{\mathrm{base}}(gh)$ is irreducible in the sense that $w_{2}^{\mathrm{base}}$ lies in the span of the right translates of any nonzero $w \in V$; and that $V$ is admissible in the sense that for every open subgroup $U \le \mathrm{GL}_2(\mathbb{Q}_p)$ there is a finite family $B$ of functions spanning all right $U$-invariant members of $V$. Let $\omega \colon \mathbb{Q}_p^{\times} \to \mathbb{C}^{\times}$ be a character with $w_{2}^{\mathrm{base}}(z\cdot g) = \omega(z)w_{2}^{\mathrm{base}}(g)$ for scalar matrices $z$, and with $\|\omega(\varpi)\| = 1$ for the uniformizer unit $\varpi$ at $p$. Let $\chi \colon \mathbb{Q}_p^{\times} \to \mathbb{C}^{\times}$ satisfy `HasConductorExponentAt ℚ p χ a`, that is, $\chi$ is trivial on the higher unit group of level $a$ while for each $m < a$ some unit of level $m$ is not killed by $\chi$, and let $\|\chi(\varpi)\| = 1$ and $2c + 1 \le a$. Finally let $w_J \in \mathrm{GL}_2(\mathbb{Q}_p)$ have matrix $\binom{0\ \ 1}{-1\ 0}$. Then, with $\mathbb{Q}_p$ given its Borel structure, for every $w \in V$ there are polynomials $P, P^{\vee} \in \mathbb{C}[X]$, integers $m, m^{\vee}$ and reals $\sigma_0, \sigma_1$ such that, writing $q = \mathrm{N}(p)$, $|\cdot|$ for the module `modulus` and $d^{\times}y$ for the pullback to $\mathbb{Q}_p^{\times}$ of the multiplicative transport `mulMeasure` of the self-dual Haar measure `selfDualHaarAt` at $p$: for $\mathrm{Re}\,s > \sigma_0$ the function $y \mapsto w(\mathrm{diag}(y,1))\chi(y)|y|^{s-1/2}$ is integrable with integral $q^{ms}P(q^{-s})$; for $\mathrm{Re}\,s < \sigma_1$ the function $y \mapsto w(\mathrm{diag}(y,1)w_J)\chi(y)^{-1}\omega(y)^{-1}|y|^{1/2-s}$ is integrable with integral $q^{m^{\vee}s}P^{\vee}(q^{-s})$; the product $\chi\omega$ again has conductor exponent $a$; and for all $s \in \mathbb{C}$ the identity of Laurent polynomials $$q^{m^{\vee}s}P^{\vee}(q^{-s}) = \big(\varepsilon(\chi\omega)q^{(1/2-s)a}\big)\big(\varepsilon(\chi)q^{(1/2-s)a}\big)\,q^{ms}P(q^{-s})$$ holds, where $\varepsilon(\nu) =$ `stdRootNumberAt ℚ p ν` is the standard local root number at $p$, the value at $s = 1/2$ of the local epsilon factor formed from the self-dual Haar measure, $\psi_p$ and the standard test function.
--
--   This is the stability of the $\mathrm{GL}_2 \times \mathrm{GL}_1$ local constants under a sufficiently deep twist (conductor exponent $a \ge 2c+1$ beyond the level of the Whittaker vector), in Whittaker-model form and under the unitarity assumptions $\|\chi(\varpi)\| = \|\omega(\varpi)\| = 1$: the twisted local functional equation of a vector in the Whittaker model has root number the product of those of $\chi$ and $\chi\omega$, with no dependence on the vector beyond the zeta polynomial. It feeds the local Rankin–Selberg computation used in the construction of the relevant $L$-functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WhittakerModel_exists_torusZeta_dual_eq_stdRootNumberAt_mul_stdRootNumberAt_mul_of_admissible_of_le_of_norm_eq_one.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker NumberField.AdelicLevel

theorem
  AutomorphicForm.WhittakerModel.exists_torusZeta_dual_eq_stdRootNumberAt_mul_stdRootNumberAt_mul_of_admissible_of_le_of_norm_eq_one
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

    (hadm : ∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
      ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
        ∀ W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
            fun g : GL (Fin 2) (p.adicCompletion ℚ) => w₂base (g * h)),
          (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) →
            W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ)))

    (ω : (p.adicCompletion ℚ)ˣ →* ℂˣ)
    (hcentral : ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
      w₂base (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω z : ℂˣ) : ℂ) * w₂base g)

    (hωu : ‖(ω (uniformizerUnit ℚ p) : ℂ)‖ = 1)

    (χ : (p.adicCompletion ℚ)ˣ →* ℂˣ) (a : ℕ)
    (hχ : LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p χ a)

    (hχu : ‖(χ (uniformizerUnit ℚ p) : ℂ)‖ = 1)
    (hdeep : 2 * c + 1 ≤ a)

    (wJ : GL (Fin 2) (p.adicCompletion ℚ))
    (hwJ : (wJ : Matrix (Fin 2) (Fin 2) (p.adicCompletion ℚ)) = !![0, 1; -1, 0]) :
    letI := localBorel ℚ p
    ∀ w ∈ Submodule.span ℂ
        (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) =>
          w₂base (g * h)),
      ∃ (P Pd : Polynomial ℂ) (m md : ℤ) (σ₀ σ₁ : ℝ),

        (∀ s : ℂ, σ₀ < s.re →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, σ₀ < s.re →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y) * ((χ y : ℂˣ) : ℂ) * ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (s - 1 / 2)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧

        (∀ s : ℂ, s.re < σ₁ →
          Integrable (fun y : (p.adicCompletion ℚ)ˣ =>
            w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((ω y : ℂˣ) : ℂ))⁻¹ *
              ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s))
            (Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) ∧
        (∀ s : ℂ, s.re < σ₁ →
          (∫ y : (p.adicCompletion ℚ)ˣ,
              w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((ω y : ℂˣ) : ℂ))⁻¹ *
                ((modulus (y : p.adicCompletion ℚ) : ℝ) : ℂ) ^ (1 / 2 - s)
              ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
            (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s))) ∧

        LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ p (χ * ω) a ∧

        (∀ s : ℂ,
          (Ideal.absNorm p.asIdeal : ℂ) ^ ((md : ℂ) * s) * Pd.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)) =
            (LanglandsTunnell.TateLocal.stdRootNumberAt ℚ p (χ * ω) *
                (((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ a) *
              (LanglandsTunnell.TateLocal.stdRootNumberAt ℚ p χ *
                (((Ideal.absNorm p.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ a) *
              ((Ideal.absNorm p.asIdeal : ℂ) ^ ((m : ℂ) * s) * P.eval ((Ideal.absNorm p.asIdeal : ℂ) ^ (-s)))) := by sorry
