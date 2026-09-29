-- Prove2me | Theorems.Thm_AutomorphicForm_lintegral_enorm_twistedConj_mul_semiLocalHaar_eq_mul_lintegral_lintegral_torus_unipotentChart_of_isTwistedSectionFnOn_of_diagonal
-- name    : AutomorphicForm.lintegral_enorm_twistedConj_mul_semiLocalHaar_eq_mul_lintegral_lintegral_torus_unipotentChart_of_isTwistedSectionFnOn_of_diagonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/3f00a214-2f8b-5d83-aadd-a13f5c0ed308
-- title:
--   Twisted orbital integrand at a diagonal element in big-cell coordinates
-- statement:
--   Let $K \subseteq L$ be number fields, $\sigma$ a $K$-automorphism of $L$, $v$ a nonzero prime of $\mathcal{O}_K$, and write $F = K_v$ and $E = L \otimes_K F$, equipped with a Borel measurable structure and an additive Haar measure $\nu$; $\sigma$ acts on $E$ through the left factor and hence entrywise on $\mathrm{GL}_2(E)$ via [`AutomorphicForm.sigmaGL`](def/AutomorphicForm_TwistedOrbital.html#L202). Let $c_G \in [0,\infty]$ be a constant expressing the Haar measure [`AutomorphicForm.semiLocalHaar`](def/AutomorphicForm_TwistedOrbital.html#L169) of $\mathrm{GL}_2(E)$ (normalised to give mass one to the semilocal integral compact set) in matrix coordinates: for every Borel $H \colon \mathrm{GL}_2(E) \to [0,\infty]$, $\int_{\mathrm{GL}_2(E)} H \, d\mu = c_G \int_{E^4} H(x)\,\bigl\|N_{E/F}(\det x)\bigr\|^{-2} d\nu^{4}(x)$, the integrand being $0$ off the locus where $\det x$ is a unit. Let $a \neq b$ in $F$ and $\gamma \in \mathrm{GL}_2(F)$ with matrix $\mathrm{diag}(a,b)$, let $A$ be the centraliser of $\{\gamma\}$ in $\mathrm{GL}_2(F)$ and $\tau$ a Haar measure on $A$ for its Borel structure. Let $\delta \in \mathrm{GL}_2(E)$ have vanishing off-diagonal entries, and let $\tau'$ be a measure on the twisted centraliser $\{t : t\,\delta\,\sigma(t)^{-1} = \delta\}$ whose image in $\mathrm{GL}_2(E)$ coincides with the image of $\tau$ under the base-change map [`AutomorphicForm.toTensorGL`](def/AutomorphicForm_TwistedOrbital.html#L71), $s \mapsto 1 \otimes s$. Let $\beta \colon \mathrm{GL}_2(E) \to \mathbb{R}$ be Borel and nonnegative with $\int_A \beta\bigl((1 \otimes t)u\bigr)\, d\tau(t) = 1$ for every $u \in \mathrm{GL}_2(E)$ with vanishing off-diagonal entries. Finally let $\varphi \colon \mathrm{GL}_2(E) \to \mathbb{C}$ be Borel and let $w$ satisfy [`AutomorphicForm.IsTwistedSectionFnOn`](def/AutomorphicForm_TwistedOrbital.html#L278), i.e. $w \geq 0$ is Borel with compact support and $\int w(tx)\, d\tau'(t) = 1$ for every $x$ with $\varphi(x^{-1}\delta\,\sigma(x)) \neq 0$. Then $$\int_{\mathrm{GL}_2(E)} \bigl\|\varphi(x^{-1}\delta\,\sigma(x))\bigr\|\, w(x)\, d\mu(x) = c_G \int_{E^2}\int_{E^2} \bigl\|\varphi\bigl((u(p)s(q))^{-1}\delta\,\sigma(u(p)s(q))\bigr)\bigr\|\, \beta(u(p))\, \bigl\|N_{E/F}(p_1p_2)\bigr\|^{-1} d\nu^2(p)\, d\nu^2(q),$$ all integrals being lower Lebesgue integrals in $[0,\infty]$, where $u(p) = \mathrm{diag}(p_1,p_2)$ and $s(q) = \begin{pmatrix} 1+q_1q_2 & q_1 \\ q_2 & 1\end{pmatrix}$, and where the inner integrand is set to $0$ unless both $\det u(p)$ and $\det s(q)$ are units.
--
--   This is the Tonelli (absolute-value) form of the unfolding of a twisted orbital integral at a diagonal element over the big cell, with the section function $w$ for the twisted centraliser traded for the section function $\beta$ for the diagonal torus; in particular the left-hand side is independent of the choice of $w$. It feeds the convergence and growth estimates for twisted orbital integrals of the indicator of the semilocal integral set.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_lintegral_enorm_twistedConj_mul_semiLocalHaar_eq_mul_lintegral_lintegral_torus_unipotentChart_of_isTwistedSectionFnOn_of_diagonal.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct TensorProduct.RightActions Classical

theorem AutomorphicForm.lintegral_enorm_twistedConj_mul_semiLocalHaar_eq_mul_lintegral_lintegral_torus_unipotentChart_of_isTwistedSectionFnOn_of_diagonal
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (cG : ENNReal)
    (hG : ∀ H : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ENNReal,
        Measurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] H →
        (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
         ∫⁻ g, H g ∂(AutomorphicForm.semiLocalHaar K L v)) =
          cG * ∫⁻ x : Fin 4 → L ⊗[K] v.adicCompletion K,
            (if h : IsUnit (!![x 0, x 1; x 2, x 3] :
                Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det then
                H (Matrix.GeneralLinearGroup.mk'' _ h) else 0) *
              ENNReal.ofReal
                ((‖Algebra.norm (v.adicCompletion K) (!![x 0, x 1; x 2, x 3] :
                    Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det‖ ^ 2)⁻¹)
            ∂(Measure.pi fun _ : Fin 4 => ν))
    (a b : v.adicCompletion K) (hab : a ≠ b)
    (γ : GL (Fin 2) (v.adicCompletion K))
    (hγ : (γ : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![a, 0; 0, b])
    (τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ)
    (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hδ₀₁ : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0)
    (hδ₁₀ : (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ))
    (hττ' : @Measure.map _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ)
        (AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)) Subtype.val τ' =
      @Measure.map _ _ (AutomorphicForm.localCentralizerBorel K v γ)
        (AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K))
        (fun s => AutomorphicForm.toTensorGL K L (v.adicCompletion K)
          (s : GL (Fin 2) (v.adicCompletion K))) τ)
    (β : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ)
    (hβm : Measurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] β) (hβ0 : ∀ x, 0 ≤ β x)
    (hβ : ∀ u : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
        (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0 →
        (u : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0 →
        (letI := AutomorphicForm.localCentralizerBorel K v γ
         ∫ t : AutomorphicForm.localCentralizer K v γ,
            β (AutomorphicForm.toTensorGL K L (v.adicCompletion K)
              (t : GL (Fin 2) (v.adicCompletion K)) * u) ∂τ) = 1)
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ)
    (hφm : Measurable[AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)] φ)
    (w : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℝ)
    (hw : AutomorphicForm.IsTwistedSectionFnOn K L (v.adicCompletion K) σ δ τ' φ w) :
    (letI := AutomorphicForm.glBorelOf (L ⊗[K] v.adicCompletion K)
     ∫⁻ x, ‖φ (x⁻¹ * δ * AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ x)‖ₑ * ENNReal.ofReal (w x)
       ∂(AutomorphicForm.semiLocalHaar K L v)) =
      cG * ∫⁻ q : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K),
        ∫⁻ p : (L ⊗[K] v.adicCompletion K) × (L ⊗[K] v.adicCompletion K),
          (if h : IsUnit (!![p.1, 0; 0, p.2] : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det then
              if h' : IsUnit (!![1 + q.1 * q.2, q.1; q.2, 1] :
                  Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)).det then
                ‖φ ((Matrix.GeneralLinearGroup.mk'' _ h * Matrix.GeneralLinearGroup.mk'' _ h')⁻¹ * δ *
                    AutomorphicForm.sigmaGL K L (v.adicCompletion K) σ
                      (Matrix.GeneralLinearGroup.mk'' _ h * Matrix.GeneralLinearGroup.mk'' _ h'))‖ₑ *
                  ENNReal.ofReal (β (Matrix.GeneralLinearGroup.mk'' _ h))
              else 0
            else 0) *
            ENNReal.ofReal ‖Algebra.norm (v.adicCompletion K) (p.1 * p.2)‖⁻¹ ∂(ν.prod ν) ∂(ν.prod ν) := by sorry
