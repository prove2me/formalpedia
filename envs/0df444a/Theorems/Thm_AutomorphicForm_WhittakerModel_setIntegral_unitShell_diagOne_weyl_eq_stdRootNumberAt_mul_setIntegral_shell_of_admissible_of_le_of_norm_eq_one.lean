-- Prove2me | Theorems.Thm_AutomorphicForm_WhittakerModel_setIntegral_unitShell_diagOne_weyl_eq_stdRootNumberAt_mul_setIntegral_shell_of_admissible_of_le_of_norm_eq_one
-- name    : AutomorphicForm.WhittakerModel.setIntegral_unitShell_diagOne_weyl_eq_stdRootNumberAt_mul_setIntegral_shell_of_admissible_of_le_of_norm_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/65fcb273-5c80-5983-bef4-4fd259114b70
-- title:
--   Unit shell at the Weyl element for a deep twist
-- statement:
--   Fix a height-one prime $p$ of $\mathcal O_{\mathbb Q}$ and let $F=\mathbb Q_p$ be the completion. Let $w_{2}:\mathrm{GL}_2(F)\to\mathbb C$ satisfy the Whittaker law $w_2\big(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}g\big)=\psi_p(x)\,w_2(g)$ for the standard local additive character $\psi_p$; let $c\in\mathbb N$ and assume $w_2$ is right invariant under the group [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) at level $p^{c}$, i.e. the preimage under the local embedding $\mathrm{GL}_2(F)\to\mathrm{GL}_2(\mathbb A_{\mathbb Q}^{\mathrm f})$ of the finite adelic level-one subgroup of level $p^{c}$; assume $w_2\neq 0$; assume the cyclicity condition that every non-zero $w$ in the $\mathbb C$-span $V$ of the right translates $g\mapsto w_2(gh)$ has $w_2$ in the span of its own right translates; and assume admissibility: for every open subgroup $U\le\mathrm{GL}_2(F)$ there is a finite set $B$ of functions such that every right $U$-invariant $W\in V$ lies in the span of $B$. Let $\omega:F^{\times}\to\mathbb C^{\times}$ be a character with $w_2(zg)=\omega(z)w_2(g)$ for scalar matrices $z$ and $|\omega(\varpi)|=1$ for the chosen uniformizer unit, and let $\chi:F^{\times}\to\mathbb C^{\times}$ satisfy $|\chi(\varpi)|=1$ and `HasConductorExponentAt` with exponent $a$, i.e. $\chi$ is trivial on the $a$-th higher unit group and non-trivial on the $m$-th for every $m<a$; assume $2c+1\le a$, and let $w_J\in\mathrm{GL}_2(F)$ have matrix $\begin{pmatrix}0&1\\-1&0\end{pmatrix}$. Then, with $F$ carrying its Borel structure and $d^{\times}y$ the measure on $F^{\times}$ obtained by pulling back along $y\mapsto y$ the measure $|x|^{-1}\,dx$ built from the self-dual additive Haar measure at $p$, for every $w\in V$ one has $$\int_{\mathrm v(y)=1} w\!\left(\mathrm{diag}(y,1)\,w_J\right)\chi(y)^{-1}\omega(y)^{-1}\,d^{\times}y=\varepsilon(\chi\omega)\,\varepsilon(\chi)\int_{\mathrm v(y)=\exp(2a)} w\!\left(\mathrm{diag}(y,1)\right)\chi(y)\,d^{\times}y,$$ where $\varepsilon(\cdot)=$ `stdRootNumberAt`, the standard local epsilon factor at $s=1/2$ formed with $\psi_p$ and the self-dual measure, and the second domain is the shell on which the valuation equals $\exp(2a)$ (additive valuation $-2a$).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WhittakerModel_setIntegral_unitShell_diagOne_weyl_eq_stdRootNumberAt_mul_setIntegral_shell_of_admissible_of_le_of_norm_eq_one.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory LanglandsTunnell.TateLocal UnramifiedWhittaker NumberField.AdelicLevel

theorem AutomorphicForm.WhittakerModel.setIntegral_unitShell_diagOne_weyl_eq_stdRootNumberAt_mul_setIntegral_shell_of_admissible_of_le_of_norm_eq_one
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
      (∫ y in {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = 1},
          w (diagOne y * wJ) * (((χ y : ℂˣ) : ℂ))⁻¹ * (((ω y : ℂˣ) : ℂ))⁻¹
          ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p)))) =
        LanglandsTunnell.TateLocal.stdRootNumberAt ℚ p (χ * ω) * LanglandsTunnell.TateLocal.stdRootNumberAt ℚ p χ *
          ∫ y in {y : (p.adicCompletion ℚ)ˣ | Valued.v (y : p.adicCompletion ℚ) = WithZero.exp (((2 * a : ℕ)) : ℤ)},
            w (diagOne y) * ((χ y : ℂˣ) : ℂ) ∂(Measure.comap Units.val (mulMeasure (selfDualHaarAt ℚ p))) := by sorry
