-- Prove2me | Theorems.Thm_AutomorphicForm_exists_pos_forall_tendsto_isTwistedOrbitalIntegralOn_mul_nhdsGT_conjAe_of_neg_of_inf_twistedCentralizer
-- name    : AutomorphicForm.exists_pos_forall_tendsto_isTwistedOrbitalIntegralOn_mul_nhdsGT_conjAe_of_neg_of_inf_twistedCentralizer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/13ff258f-9b82-5075-9e65-45e40861ec2b
-- title:
--   Twisted orbital integrals tend to κ I' for c<0
-- statement:
--   Work in $G=\mathrm{GL}_2(\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R})$ with its Borel structure, with $\sigma$ the automorphism induced by complex conjugation on the left factor, so that the norm string of $\delta$ is $N\delta=\delta\,\sigma(\delta)$ (the product over $i<[\mathbb{C}:\mathbb{R}]=2$ of $\sigma^i\delta$) and the twisted centraliser of $\delta$ is the closed subgroup $T'_\delta=\{t: t\,\delta\,\sigma(t)^{-1}=\delta\}$. Given a Haar measure $\mu_L$ on $G$, a unit $c\in\mathbb{R}^\times$ with $c<0$, elements $\delta,y\in G$ such that the image of the scalar matrix $c\cdot 1$ under $\mathrm{GL}_2(\mathbb{R})\to G$ equals $y^{-1}(N\delta)y$, a Haar measure $\tau'$ on $T'_\delta$, an element $u_0\in G$ and a Haar measure $\tau_S$ on $S:=T'_\delta\cap T'_{u_0\delta}$, the assertion is that there exists $\kappa>0$ with the following two properties. First, $\kappa$ is the $(\tau',\tau_S)$-covolume of $S$ in $T'_\delta$ in Weil's sense: every non-negative measurable compactly supported $w$ on $T'_\delta$ with $\int_S w(st)\,d\tau_S(s)=1$ for all $t\in T'_\delta$ satisfies $\int_{T'_\delta} w\,d\tau'=\kappa$. Second, let $\varphi:\mathrm{GL}_2(\mathbb{C})\to\mathbb{C}$ be compactly supported and given by a $C^\infty$ function of the matrix entries; let $\theta_0>0$ and let $u:\mathbb{R}\to G$ take values in $S$, tend to $1$ as $\theta\to 0^+$, and satisfy that $N(u(\theta)\delta)$ is regular semisimple (its $\mathrm{tr}^2-4\det$ is a unit) for $\theta\in(0,\theta_0)$; let $\tau_{u(\theta)}$ be Haar on $T'_{u(\theta)\delta}$ for such $\theta$, with the same image measure on $G$ as $\tau_S$. Transport $\varphi$ to $G$ along $\mathbb{C}\otimes_{\mathbb{R}}\mathbb{R}\cong\mathbb{C}$. If $\Psi(\theta)$ is a value of the twisted orbital integral of this function at $u(\theta)\delta$ relative to $\tau_{u(\theta)}$ for each $\theta\in(0,\theta_0)$, and $I'$ is such a value at $\delta$ relative to $\tau'$ — that is, $\Psi(\theta)$, resp. $I'$, equals $\int_G \varphi(x^{-1}\gamma\,\sigma(x))\,w(x)\,d\mu_L$ for some non-negative measurable compactly supported $w$ whose translates integrate to $1$ over the relevant twisted centraliser at every $x$ where the integrand is non-zero — then $\Psi(\theta)\to\kappa\,I'$ as $\theta\to 0^+$.
--
--   This is the archimedean limit computation for twisted orbital integrals at a norm-central class of the second kind ($c<0$, where $T'_\delta$ is compact modulo its centre), in the base-change comparison for $\mathrm{GL}_2$ over $\mathbb{C}/\mathbb{R}$: degeneration along a path inside the torus $S$ produces the singular twisted orbital integral multiplied by the covolume $\kappa$. It is used in the two statements identifying the twisted orbital integral at $\delta$ with an ordinary orbital integral at the scalar $c\cdot 1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_pos_forall_tendsto_isTwistedOrbitalIntegralOn_mul_nhdsGT_conjAe_of_neg_of_inf_twistedCentralizer.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_pos_forall_tendsto_isTwistedOrbitalIntegralOn_mul_nhdsGT_conjAe_of_neg_of_inf_twistedCentralizer
    (μL : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
    (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μL)
    (c : ℝˣ) (hc : (c : ℝ) < 0)
    (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
    (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
      (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ')
    (u₀ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (τS : @Measure ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) (borel _))
    (hτS : @Measure.IsHaarMeasure _ _ _ (borel _) τS) :
    ∃ κ : ℝ, 0 < κ ∧
      (∀ w : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) → ℝ,
        (letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
         letI : MeasurableSpace ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓
             twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) := borel _
         (∀ t, 0 ≤ w t) ∧ Measurable w ∧ HasCompactSupport w ∧
           ∀ t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ),
             ∫ s : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)),
               w ((⟨(s : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)), (Subgroup.mem_inf.mp s.2).1⟩ :
                 ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)) * t) ∂τS = 1) →
        (letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
         ∫ t, w t ∂τ' = κ)) ∧
      ∀ (φ : GL (Fin 2) ℂ → ℂ),
        ((∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
          ∀ g, φ g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φ) →
      ∀ (θ₀ : ℝ), 0 < θ₀ →
      ∀ (u : ℝ → GL (Fin 2) (ℂ ⊗[ℝ] ℝ)),
        (∀ θ : ℝ, u θ ∈ twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓ twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) →
        (letI := glBorelOf (ℂ ⊗[ℝ] ℝ)
         Filter.Tendsto u (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)) →
        (∀ θ ∈ Set.Ioo 0 θ₀, IsRegularSemisimple (normString ℝ ℂ ℝ Complex.conjAe (u θ * δ))) →
      ∀ (τu : ∀ θ : ℝ, @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u θ * δ))
          (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ))),
        (∀ θ ∈ Set.Ioo 0 θ₀, @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ)) (τu θ)) →
        (∀ θ ∈ Set.Ioo 0 θ₀,
          (letI := glBorelOf (ℂ ⊗[ℝ] ℝ)
           letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe (u θ * δ)
           letI : MeasurableSpace ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ ⊓
               twistedCentralizer ℝ ℂ ℝ Complex.conjAe (u₀ * δ)) := borel _
           Measure.map Subtype.val (τu θ) = Measure.map Subtype.val τS)) →
      ∀ (Ψ : ℝ → ℂ),
        (∀ θ ∈ Set.Ioo 0 θ₀,
          IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL (u θ * δ) (τu θ)
            (fun z => φ (Matrix.GeneralLinearGroup.map
                (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                  (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) (Ψ θ)) →
      ∀ I' : ℂ,
        IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
            (fun z => φ (Matrix.GeneralLinearGroup.map
                (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                  (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
        Filter.Tendsto Ψ (nhdsWithin 0 (Set.Ioi 0)) (nhds ((κ : ℂ) * I')) := by sorry
