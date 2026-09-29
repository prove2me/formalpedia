-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isNormConjugator_and_coupled_of_gram_of_algHom_complex
-- name    : AutomorphicForm.exists_isNormConjugator_and_coupled_of_gram_of_algHom_complex
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/3a72dc01-5cf4-5551-9771-9e16883e52ef
-- title:
--   Gram normalisation couples central measures at a split complex place
-- statement:
--   Let $K$ and $L$ be fields with $L$ a finite-dimensional $K$-algebra of prime degree $\ell = \operatorname{finrank}_K L$, let $\sigma$ be a $K$-algebra automorphism of $L$ with $\sigma \neq 1$, let $\mathbb{C}$ be endowed with a $K$-algebra structure, and let $\iota : L \to \mathbb{C}$ be a $K$-algebra homomorphism. Fix $c \in \mathbb{C}^\times$, write $\gamma = c \cdot 1 \in \mathrm{GL}_2(\mathbb{C})$, and let $\delta, y \in \mathrm{GL}_2(L \otimes_K \mathbb{C})$ satisfy `IsNormConjugator`: the entrywise image of $\gamma$ under $x \mapsto 1 \otimes x$ equals $y^{-1} \bigl(\prod_{i=0}^{\ell-1} \sigma^i(\delta)\bigr) y$, where $\sigma$ acts on $\mathrm{GL}_2(L \otimes_K \mathbb{C})$ entrywise through $\sigma \otimes \mathrm{id}$. Let $\tau$ be a Haar measure on the centraliser of $\{\gamma\}$ in $\mathrm{GL}_2(\mathbb{C})$ and $\tau'$ a Haar measure on the twisted centraliser $\{t \mid t\,\delta\,\sigma(t)^{-1} = \delta\}$ in $\mathrm{GL}_2(L \otimes_K \mathbb{C})$, both with their Borel $\sigma$-algebras. Assume the common Gram normalisation `hgram`: there are $n_1, n_2 \in \mathbb{N}$, $\mathbb{R}$-linearly independent families $e_1 : \mathrm{Fin}\,n_1 \to M_2(L \otimes_K \mathbb{C})$ and $e_2 : \mathrm{Fin}\,n_2 \to M_2(L \otimes_K \mathbb{C})$ spanning, respectively, the entrywise image of $M_2(\mathbb{C})$ under $x \mapsto 1 \otimes x$ and the $\sigma$-twisted commutant $\{X \mid X\delta = \delta\,\sigma(X)\}$, and a scalar $s \in (0,\infty)$ in `ENNReal` (so $s \neq 0$, $s \neq \infty$), such that the pushforward of $\tau$ to $M_2(L \otimes_K \mathbb{C})$ (via $t \mapsto 1 \otimes t$ entrywise) and the pushforward of $\tau'$ to $M_2(L \otimes_K \mathbb{C})$ are each $s$ times the measure obtained from Lebesgue measure on the coordinates of the corresponding family, rescaled by $\sqrt{|\det(\operatorname{Tr}_{(L \otimes_K \mathbb{C})/\mathbb{R}}(\operatorname{tr}(e_i e_j)))|}$ and given density $X \mapsto |N_{(L \otimes_K \mathbb{C})/\mathbb{R}}(\det X)|^{-1}$. The conclusion is that some $y' \in \mathrm{GL}_2(L \otimes_K \mathbb{C})$ is again a norm conjugator in the above sense for $\gamma$ and $\delta$, and in addition couples the two measures: the pushforward of $\tau'$ along $t \mapsto y'^{-1} t y'$ coincides with the pushforward of $\tau$ along $t \mapsto 1 \otimes t$.
--
--   This is the archimedean split case of the measure-matching step in the twisted (base-change) comparison of orbital integrals for $\mathrm{GL}_2$: a common Gram-type normalisation of Haar measures on the centraliser of a central element and on the $\sigma$-twisted centraliser of $\delta$ forces the existence of a norm conjugator transporting one measure to the other. It is used in the assembly of the identity expressing a twisted orbital integral at a central class as $\pm$ the corresponding orbital integral of the scalar at archimedean places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isNormConjugator_and_coupled_of_gram_of_algHom_complex.lean

import Definitions.Def_AutomorphicForm_SplitFibreIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isNormConjugator_and_coupled_of_gram_of_algHom_complex
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hdeg : (Module.finrank K L).Prime) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    [Algebra K ℂ] (ι : L →ₐ[K] ℂ)
    (c : ℂˣ)
    (δ y : GL (Fin 2) (L ⊗[K] ℂ))
    (hδ : IsNormConjugator K L ℂ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ : @Measure (Subgroup.centralizer
        ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℂ)))
        (centralizerBorel ℂ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
    (τ' : @Measure (twistedCentralizer K L ℂ σ δ) (twistedCentralizerBorel K L ℂ σ δ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℂ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ)
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℂ σ δ) τ')
    (hgram : (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] ℂ)) := borel _
       letI := centralizerBorel ℂ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
       letI := twistedCentralizerBorel K L ℂ σ δ
       ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (L ⊗[K] ℂ))
         (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] ℂ)) (s : ENNReal),
         s ≠ 0 ∧ s ≠ ⊤ ∧
         LinearIndependent ℝ e₁ ∧
           (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] ℂ))) =
             Set.range (fun Y : Matrix (Fin 2) (Fin 2) ℂ =>
               Y.map (fun x : ℂ => ((1 : L) ⊗ₜ[K] x : L ⊗[K] ℂ))) ∧
         LinearIndependent ℝ e₂ ∧
           (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] ℂ))) =
             {X | X * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] ℂ)) =
               (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] ℂ)) * X.map (sigmaTensor K L ℂ σ)} ∧
         Measure.map (fun t : ↥(Subgroup.centralizer
               ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℂ))) =>
             ((t : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).map
               (fun x : ℂ => ((1 : L) ⊗ₜ[K] x : L ⊗[K] ℂ))) τ =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                   Algebra.trace ℝ (L ⊗[K] ℂ) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                 Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] ℂ) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
         Measure.map (fun t : ↥(twistedCentralizer K L ℂ σ δ) =>
             ((t : GL (Fin 2) (L ⊗[K] ℂ)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] ℂ))) τ' =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                   Algebra.trace ℝ (L ⊗[K] ℂ) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                 Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] ℂ) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))) :
    ∃ y' : GL (Fin 2) (L ⊗[K] ℂ),
      IsNormConjugator K L ℂ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y' ∧
      Coupled K L ℂ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y' τ τ' := by sorry
