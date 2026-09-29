-- Prove2me | Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_isTwistedOrbitalIntegralOn_conjAe_imp_eq
-- name    : AutomorphicForm.exists_contDiff_hasCompactSupport_forall_isTwistedOrbitalIntegralOn_conjAe_imp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/55711ee5-a1bf-5a50-8e81-a073a916ef37
-- title:
--   Archimedean transfer of twisted orbital integrals on GL₂
-- statement:
--   Let $P$ be a real normed vector space, let $\mu_A$ be a Haar measure on $\mathrm{GL}_2(\mathbb{R})$ and $\mu_L$ a Haar measure on $\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$, both for the Borel structure `glBorelOf`. Let $\Phi$ be a complex-valued function of a pair (complex $2\times2$ entry matrix, parameter in $P$) which is $C^\infty$ over $\mathbb{R}$, has compact support, has $\mathrm{tsupport}$ contained in the pairs whose matrix has unit determinant, and whose right translates and left translates in the matrix variable by the elements of the group `rowIsometrySubgroup₀ ℂ` each span a finite-dimensional $\mathbb{C}$-subspace of functions. Then there exists $F$, a complex-valued function of a real $2\times2$ entry matrix and a parameter in $P$, again $C^\infty$, compactly supported, with $\mathrm{tsupport}$ inside the pairs of invertible determinant, and with finite-dimensional spans of its right and of its left translates by `rowIsometrySubgroup₀ ℝ`, such that: (a) for every $n$, all $c:\mathrm{Fin}\,n\to\mathbb{C}$ and $q:\mathrm{Fin}\,n\to P$, if $\sum_j c_j\Phi(E,q_j)=0$ for every complex entry matrix $E$, then $\sum_j c_j F(E',q_j)=0$ for every real entry matrix $E'$; (b) for every $p\in P$ and every $\gamma\in \mathrm{GL}_2(\mathbb{R})$ which is regular semisimple in the sense that $\mathrm{tr}(\gamma)^2-4\det(\gamma)$ is a unit, every $\delta\in\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ whose twisted norm `normString` for $\sigma=$ complex conjugation equals the image `toTensorGL` $\gamma$ of $\gamma$ exactly (conjugator $y=1$), and all Haar measures $\tau$ on the centraliser of $\gamma$ and $\tau'$ on the $\sigma$-twisted centraliser $\{t: t\delta\sigma(t)^{-1}=\delta\}$ of $\delta$ that are `Coupled` with $y=1$, i.e. the pushforward of $\tau'$ under the inclusion equals the pushforward of $\tau$ under `toTensorGL`: any $I'\in\mathbb{C}$ representing the twisted orbital integral $\int \varphi(x^{-1}\delta\sigma(x))\,w(x)\,d\mu_L$ of $\varphi(y)=\Phi$ of the matrix of $y$ read through $\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R}\cong\mathbb{C}$ at the parameter $p$, against an admissible weight $w$, coincides with any $I\in\mathbb{C}$ representing the orbital integral $\int F(x^{-1}\gamma x,p)\,w(x)\,d\mu_A$ of $F(\cdot,p)$ at $\gamma$; and (c) for every $p$ and every regular semisimple $\gamma$ that is not the twisted norm of any $\delta$, and every Haar $\tau$ on the centraliser of $\gamma$, every value $I$ of the orbital integral of $F(\cdot,p)$ at $\gamma$ against $\mu_A$ and $\tau$ vanishes.
--
--   This is the archimedean base-change transfer at a real place, in a version with parameters: a smooth compactly supported function on $\mathrm{GL}_2(\mathbb{C}\otimes_\mathbb{R}\mathbb{R})$ is matched, parameter slice by parameter slice and compatibly with linear relations in the parameter, by a function on $\mathrm{GL}_2(\mathbb{R})$ whose orbital integrals equal the twisted orbital integrals at exact norms and vanish at regular semisimple classes that are not norms. It feeds the construction of an archimedean test factor used in the comparison of twisted and untwisted trace formulae.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_isTwistedOrbitalIntegralOn_conjAe_imp_eq.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_contDiff_hasCompactSupport_forall_isTwistedOrbitalIntegralOn_conjAe_imp_eq
    (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
    (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
    (μL : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ)
    (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
    (hΦU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))})
    (hΦr : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℂ =>
      fun q : (Fin 2 → Fin 2 → ℂ) × P =>
        Φ (Matrix.of.symm (Matrix.of q.1 * ((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)), q.2))))
    (hΦl : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℂ =>
      fun q : (Fin 2 → Fin 2 → ℂ) × P =>
        Φ (Matrix.of.symm (((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.of q.1), q.2))))
    (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
    (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μL) :
    ∃ F : (Fin 2 → Fin 2 → ℝ) × P → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧ tsupport F ⊆ {r | IsUnit (Matrix.det (Matrix.of r.1))} ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℝ =>
        fun r : (Fin 2 → Fin 2 → ℝ) × P =>
          F (Matrix.of.symm (Matrix.of r.1 * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)), r.2))) ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℝ =>
        fun r : (Fin 2 → Fin 2 → ℝ) × P =>
          F (Matrix.of.symm (((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of r.1), r.2))) ∧
      (∀ (n : ℕ) (c : Fin n → ℂ) (q : Fin n → P),
        (∀ E : Fin 2 → Fin 2 → ℂ, ∑ j, c j * Φ (E, q j) = 0) →
          ∀ E' : Fin 2 → Fin 2 → ℝ, ∑ j, c j * F (E', q j) = 0) ∧
      (∀ p : P, ∀ γ : GL (Fin 2) ℝ, IsRegularSemisimple γ →
        ∀ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsNormConjugator ℝ ℂ ℝ Complex.conjAe γ δ 1 →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ))
          (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
          Coupled ℝ ℂ ℝ Complex.conjAe γ δ 1 τ τ' →
          ∀ I I' : ℂ,
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
              (fun y => Φ (Matrix.of.symm
                ((Matrix.GeneralLinearGroup.map
                  (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                    (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom y : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ),
                p)) I' →
            IsOrbitalIntegralOn ℝ μA γ τ (fun g => F (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℝ), p)) I →
            I' = I) ∧
      (∀ p : P, ∀ γ : GL (Fin 2) ℝ, IsRegularSemisimple γ → (¬ ∃ δ, IsNormOf ℝ ℂ ℝ Complex.conjAe γ δ) →
        ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
          ∀ I : ℂ, IsOrbitalIntegralOn ℝ μA γ τ (fun g => F (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℝ), p)) I →
            I = 0) := by sorry
