-- Prove2me | Theorems.Thm_AutomorphicForm_exists_chart_map_val_eq_smul_withDensity_of_gram_conjAe_of_neg
-- name    : AutomorphicForm.exists_chart_map_val_eq_smul_withDensity_of_gram_conjAe_of_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/6cd756f5-4e9d-560b-8f9d-42968a91e9d9
-- title:
--   Quaternionic twisted centraliser measure in an ℝ⁴ chart
-- statement:
--   Work with $K=\mathbb{R}$, $L=\mathbb{C}$, $A=\mathbb{R}$ and $\sigma$ complex conjugation, so that the ambient algebra is $\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R}$ and `sigmaTensor` is $\bar{\cdot}\otimes\mathrm{id}$. Let $c$ be a unit of $\mathbb{R}$ with $c<0$, and let $\delta,y\in GL_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ satisfy `IsNormConjugator`, i.e. the image of the scalar matrix $c\cdot 1$ under $GL_2(\mathbb{R})\to GL_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ equals $y^{-1}\,\delta\,\sigma(\delta)\,y$ (the norm string has two factors since $[\mathbb{C}:\mathbb{R}]=2$). Let $\tau'$ be a measure, for the Borel structure, on the twisted centraliser $\{t : t\delta\sigma(t)^{-1}=\delta\}$. Let $e_2:\mathrm{Fin}\,n_2\to M_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ and $s\in[0,\infty]$ be such that: $e_2$ is $\mathbb{R}$-linearly independent; its $\mathbb{R}$-span is exactly $\{X : X\delta=\delta\,\sigma(X)\}$; and the push-forward of $\tau'$ along $t\mapsto$ its underlying matrix equals $s$ times the measure $\sqrt{|\det G|}\cdot(a\mapsto\sum_i a_i e_2(i))_*\mathrm{Leb}_{\mathbb{R}^{n_2}}$, with $G_{ij}=\mathrm{Tr}_{\mathbb{C}\otimes\mathbb{R}/\mathbb{R}}(\mathrm{tr}(e_2(i)e_2(j)))$, weighted by the density $|N_{\mathbb{C}\otimes\mathbb{R}/\mathbb{R}}(\det X)|^{-1}$. Then there is an injective $\mathbb{R}$-linear map $\varphi:\mathbb{R}^4\to M_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ with $\det\varphi(a)=1\otimes(a_0^2+a_1^2-c(a_2^2+a_3^2))$ for all $a$, such that the same push-forward of $\tau'$ equals $16|c|\,s$ times $\varphi_*\mathrm{Leb}_{\mathbb{R}^4}$ weighted by $|N_{\mathbb{C}\otimes\mathbb{R}/\mathbb{R}}(\det X)|^{-1}$.
--
--   This is the anisotropic (quaternionic) normalisation step in the measure-theoretic bookkeeping for twisted centralisers attached to a norm-conjugacy class in $GL_2$ over $\mathbb{C}/\mathbb{R}$: an arbitrary Gram-normalised presentation of the twisted centraliser's Lie-type space is replaced by a fixed linear chart of $\mathbb{R}^4$ whose determinant is the anisotropic quaternary form $a_0^2+a_1^2-c(a_2^2+a_3^2)$, at the cost of the explicit constant $16|c|$. It is used by [`AutomorphicForm.twistedCentralizer_detShell_eq_of_gram_conjAe_of_neg`](thm.html#AutomorphicForm.twistedCentralizer_detShell_eq_of_gram_conjAe_of_neg), which evaluates the resulting measure on determinant shells.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_chart_map_val_eq_smul_withDensity_of_gram_conjAe_of_neg.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_chart_map_val_eq_smul_withDensity_of_gram_conjAe_of_neg
    (c : ℝˣ) (hc : (c : ℝ) < 0)
    (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (n₂ : ℕ) (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) (s : ENNReal)
    (hgram₂ : (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borel _
       letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
       LinearIndependent ℝ e₂ ∧
           (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
             {X | X * (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) =
               (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) * X.map (sigmaTensor ℝ ℂ ℝ Complex.conjAe)} ∧
         Measure.map (fun t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) =>
             ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) τ' =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                   Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                 Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))) :
    letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borel _
    letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
    ∃ φ : (Fin 4 → ℝ) →ₗ[ℝ] Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ),
      Function.Injective φ ∧
      (∀ a : Fin 4 → ℝ, Matrix.det (φ a) = ((1 : ℂ) ⊗ₜ[ℝ] (a 0 ^ 2 + a 1 ^ 2 - (c : ℝ) * (a 2 ^ 2 + a 3 ^ 2)) : ℂ ⊗[ℝ] ℝ)) ∧
      Measure.map (fun t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) =>
          ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) τ' =
        (ENNReal.ofReal (16 * |(c : ℝ)|) * s) •
          (Measure.map φ (volume : Measure (Fin 4 → ℝ))).withDensity
            (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) => (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) := by sorry
