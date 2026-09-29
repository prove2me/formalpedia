-- Prove2me | Theorems.Thm_AutomorphicForm_ofReal_mul_inf_twistedCentralizer_detBand_eq_twistedCentralizer_detShell_of_weilConst
-- name    : AutomorphicForm.ofReal_mul_inf_twistedCentralizer_detBand_eq_twistedCentralizer_detShell_of_weilConst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/1f5b0134-bf79-5e32-b484-81702f6554b6
-- title:
--   Weil constant times band mass equals shell mass
-- statement:
--   Fix a unit $c$ of $\mathbb{R}$ with $c<0$ and elements $\delta, y \in \mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ such that the image of the scalar matrix $c\cdot 1$ under the base-change homomorphism $\mathrm{GL}_2(\mathbb{R}) \to \mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ equals $y^{-1}\,\delta\,\sigma(\delta)\,y$, where $\sigma$ is the map induced on $\mathrm{GL}_2$ by complex conjugation on the tensor factor (the norm string has two factors, $\mathrm{finrank}_{\mathbb{R}}\mathbb{C}=2$). Write $T'_\delta=\{t : t\delta\sigma(t)^{-1}=\delta\}$ for the twisted centraliser, and, for $u_0 \in \mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$, put $S = T'_\delta \cap T'_{u_0\delta}$; both carry their Borel $\sigma$-algebras. Let $\tau'$ be a Haar measure on $T'_\delta$ and $\tau_S$ a Haar measure on $S$, and let $\kappa>0$ be a real number such that $\int w\,\mathrm{d}\tau' = \kappa$ for every non-negative measurable compactly supported $w : T'_\delta \to \mathbb{R}$ all of whose fibre integrals $\int_S w(s t)\,\mathrm{d}\tau_S(s)$, $t \in T'_\delta$, equal $1$. Let $B_S=\{s\in S : \det s = 1\otimes d \text{ for some } d\in[1,e^2]\}$ and assume $0<\tau_S(B_S)<\infty$. Then $\mathrm{ofReal}(\kappa)\cdot\tau_S(B_S) = \tau'\{t\in T'_\delta : \det t = 1\otimes d \text{ for some } d\in[1,e^2]\}$, an identity in $[0,\infty]$.
--
--   This identifies the $(\tau',\tau_S)$-Weil constant as the ratio of the $\tau'$-mass of the determinant shell in the twisted centraliser $T'_\delta$ to the $\tau_S$-mass of the corresponding band in the subgroup $S = T'_\delta\cap T'_{u_0\delta}$, in the second-kind case $c<0$ at the real place. It feeds the sign bookkeeping for twisted orbital integrals, being used in the derivation of the relation $\alpha\kappa m = -1$ recorded by [`AutomorphicForm.hcConst_mul_weilConst_mul_eq_neg_one_of_gram_conjAe_of_coupled_of_neg`](thm.html#AutomorphicForm.hcConst_mul_weilConst_mul_eq_neg_one_of_gram_conjAe_of_coupled_of_neg).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_ofReal_mul_inf_twistedCentralizer_detBand_eq_twistedCentralizer_detShell_of_weilConst.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_GL2RealOrbitalTransforms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm AutomorphicForm.GL2Real
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.ofReal_mul_inf_twistedCentralizer_detBand_eq_twistedCentralizer_detShell_of_weilConst
    (c : ℝˣ) (hc : (c : ℝ) < 0)
    (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ')
    (u₀ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (τS : @Measure ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) (borel _))
    (hτS : @Measure.IsHaarMeasure _ _ _ (borel _) τS)
    (κ : ℝ) (hκ0 : 0 < κ)
    (hκ : ∀ w : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) → ℝ,
      (letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
       letI : MeasurableSpace ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓
           twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) := borel _
       (∀ t, 0 ≤ w t) ∧ Measurable w ∧ HasCompactSupport w ∧
         ∀ t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ),
           ∫ s : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)),
             w ((⟨(s : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)), (Subgroup.mem_inf.mp s.2).1⟩ :
               ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)) * t) ∂τS = 1) →
      (letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
       ∫ t, w t ∂τ' = κ))
    (hpos : 0 < τS {t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) |
        ∃ d ∈ Set.Icc (1 : ℝ) (Real.exp 2),
        Matrix.det ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) = ((1 : ℂ) ⊗ₜ[ℝ] d : ℂ ⊗[ℝ] ℝ)})
    (hfin : τS {t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) |
        ∃ d ∈ Set.Icc (1 : ℝ) (Real.exp 2),
        Matrix.det ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) = ((1 : ℂ) ⊗ₜ[ℝ] d : ℂ ⊗[ℝ] ℝ)} < ⊤) :
    ENNReal.ofReal κ * τS {t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) |
        ∃ d ∈ Set.Icc (1 : ℝ) (Real.exp 2),
        Matrix.det ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) = ((1 : ℂ) ⊗ₜ[ℝ] d : ℂ ⊗[ℝ] ℝ)} =
      τ' {t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) | ∃ d ∈ Set.Icc (1 : ℝ) (Real.exp 2),
        Matrix.det ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) = ((1 : ℂ) ⊗ₜ[ℝ] d : ℂ ⊗[ℝ] ℝ)} := by sorry
