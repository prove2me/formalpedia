-- Prove2me | Theorems.Thm_AutomorphicForm_isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_complex_of_nhds_forall_isRegularSemisimple
-- name    : AutomorphicForm.isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_complex_of_nhds_forall_isRegularSemisimple
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/e9987f9b-7e77-5a51-a66c-64fff2ae6deb
-- title:
--   Central transfer at a split complex place
-- statement:
--   Let $L/K$ be a finite extension of fields whose degree $n=\operatorname{finrank}_K L$ is prime, let $\sigma$ be a $K$-algebra automorphism of $L$ with $\sigma\neq 1$, let $\mathbb{C}$ carry a $K$-algebra structure and let $\iota\colon L\to\mathbb{C}$ be a $K$-algebra map. Fix Haar measures $\mu_A$ on $\mathrm{GL}_2(\mathbb{C})$ and $\mu_L$ on $\mathrm{GL}_2(L\otimes_K\mathbb{C})$, both for the Borel $\sigma$-algebras. Let $\varphi\colon \mathrm{GL}_2(L\otimes_K\mathbb{C})\to\mathbb{C}$ be compactly supported and smooth in split coordinates, i.e. $\varphi(g)=\Phi$ applied to the matrix entries of the $n$ components of `SplitPlace.psiGL` $(g)$ for some $C^\infty$ function $\Phi$ on $\mathrm{Fin}\,n\to$ (2$\times 2$ complex matrices), where `psiGL` is the isomorphism $\mathrm{GL}_2(L\otimes_K\mathbb{C})\cong(\mathrm{Fin}\,n\to\mathrm{GL}_2(\mathbb{C}))$ coming from the $\sigma$-coordinate splitting of $L\otimes_K\mathbb{C}$ determined by $\iota$; let $f\colon\mathrm{GL}_2(\mathbb{C})\to\mathbb{C}$ be compactly supported and given by a $C^\infty$ function of the matrix entries; and let $c\in\mathbb{C}^\times$. The matching hypothesis asserts the existence of a neighbourhood $V$ of the scalar matrix $c\cdot 1$ in $\mathrm{GL}_2(\mathbb{C})$ such that: whenever the norm string $\mathrm{N}\delta=\delta\,\sigma(\delta)\cdots\sigma^{n-1}(\delta)$ of $\delta\in\mathrm{GL}_2(L\otimes_K\mathbb{C})$ is regular semisimple (its trace squared minus four times its determinant is a unit), $\gamma\in V$ is regular semisimple, $y$ satisfies $\gamma\otimes 1=y^{-1}(\mathrm{N}\delta)y$, and $\tau$, $\tau'$ are Haar measures on the centraliser of $\gamma$ in $\mathrm{GL}_2(\mathbb{C})$ and on the $\sigma$-twisted centraliser $\{t: t\delta\sigma(t)^{-1}=\delta\}$ which are coupled (the image of $\tau'$ under $t\mapsto y^{-1}ty$ equals the image of $\tau$ under base change $t\mapsto t\otimes 1$), then every twisted orbital value $I'$ of $\varphi$ at $\delta$ for $\mu_L,\tau'$ equals every orbital value $I$ of $f$ at $\gamma$ for $\mu_A,\tau$. The conclusion is that for all $\delta,y$ with $(c\cdot 1)\otimes 1=y^{-1}(\mathrm{N}\delta)y$, all coupled Haar pairs $\tau$ on the centraliser of $c\cdot 1$ and $\tau'$ on the twisted centraliser of $\delta$, and every $I'\in\mathbb{C}$ that is a twisted orbital value of $\varphi$ at $\delta$ — that is, $I'=\int \varphi(x^{-1}\delta\,\sigma(x))w(x)\,d\mu_L$ for some admissible non-negative compactly supported measurable weight $w$ normalised along the twisted centraliser orbits — the same number $I'$ is an orbital value of $f$ at the scalar $c\cdot 1$: $I'=\int f(x^{-1}(c\cdot 1)x)w'(x)\,d\mu_A$ for some weight $w'$ with the corresponding normalisation against $\tau$.
--
--   This is the central (scalar) identity of the local comparison of orbital and twisted orbital integrals at a split archimedean place, in the complex model: matching of $\varphi$ and $f$ at the regular semisimple classes near a scalar forces the matching of values at the scalar class itself. It feeds the archimedean matching statements [`AutomorphicForm.areMatchingArch_central_transfer_of_scalar`](thm.html#AutomorphicForm.areMatchingArch_central_transfer_of_scalar) and [`AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_finrank_eq_two`](thm.html#AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_finrank_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_complex_of_nhds_forall_isRegularSemisimple.lean

import Definitions.Def_AutomorphicForm_SplitFibreIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isOrbitalIntegralOn_scalar_of_isTwistedOrbitalIntegralOn_of_algHom_complex_of_nhds_forall_isRegularSemisimple
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    [Algebra K ℂ] (ι : L →ₐ[K] ℂ)
    (μA : @Measure (GL (Fin 2) ℂ) (glBorelOf ℂ))
    (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℂ) μA)
    (μL : @Measure (GL (Fin 2) (L ⊗[K] ℂ)) (glBorelOf (L ⊗[K] ℂ)))
    (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] ℂ)) μL)
    (φ : GL (Fin 2) (L ⊗[K] ℂ) → ℂ)
    (hφ : (∃ Φ : (Fin (Module.finrank K L) → Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ g, φ g = Φ (fun k i j =>
        ((SplitPlace.psiGL ℂ σ ι hdeg hσ g k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧
      HasCompactSupport φ)
    (f : GL (Fin 2) ℂ → ℂ)
    (hf : (∃ F : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport f)
    (c : ℂˣ)
    (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
      ∀ δ : GL (Fin 2) (L ⊗[K] ℂ), IsRegularSemisimple (normString K L ℂ σ δ) →
      ∀ γ ∈ V, IsRegularSemisimple γ →
      ∀ y : GL (Fin 2) (L ⊗[K] ℂ), IsNormConjugator K L ℂ σ γ δ y →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℂ))) (centralizerBorel ℂ γ))
        (τ' : @Measure (twistedCentralizer K L ℂ σ δ) (twistedCentralizerBorel K L ℂ σ δ)),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℂ γ) τ →
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℂ σ δ) τ' →
        Coupled K L ℂ σ γ δ y τ τ' →
        ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L ℂ σ μL δ τ' φ I' →
          IsOrbitalIntegralOn ℂ μA γ τ f I → I' = I) :
    ∀ δ y : GL (Fin 2) (L ⊗[K] ℂ),
      IsNormConjugator K L ℂ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y →
      ∀ (τ : @Measure (Subgroup.centralizer
            ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℂ)))
            (centralizerBorel ℂ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
        (τ' : @Measure (twistedCentralizer K L ℂ σ δ) (twistedCentralizerBorel K L ℂ σ δ)),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℂ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℂ σ δ) τ' →
        Coupled K L ℂ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ' →
        ∀ I' : ℂ, IsTwistedOrbitalIntegralOn K L ℂ σ μL δ τ' φ I' →
          IsOrbitalIntegralOn ℂ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I' := by sorry
