-- Prove2me | Theorems.Thm_AutomorphicForm_semilocal_central_transfer_of_forall_oneplace_of_referenceMeasures
-- name    : AutomorphicForm.semilocal_central_transfer_of_forall_oneplace_of_referenceMeasures
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/6ddcfb4e-b306-5b33-92c3-1d255727ae14
-- title:
--   Semi-local central transfer with reference measures and per-place factors
-- statement:
--   The setting is a finite extension $K \subseteq L$ of fields with $L/K$ finite-dimensional, together with a $K$-algebra automorphism $\sigma$ of $L$, and a finite index set $\iota$ with decidable equality. For each $i \in \iota$ a commutative $K$-algebra $A_i$ is given which is a Hausdorff, locally compact, second countable topological ring; $X_i$ and $Y_i$ are finite-dimensional real normed spaces, and $\varepsilon^K_i : \mathrm{GL}_2(A_i) \to X_i$, $\varepsilon^L_i : \mathrm{GL}_2(L \otimes_K A_i) \to Y_i$ are continuous 'coordinate readings' (continuity being the hypotheses `hεK`, `hεL`). For each $i$ a unit $c_i \in A_i^\times$ is fixed; the associated central element is the scalar matrix $\mathrm{scalar}(c_i) \in \mathrm{GL}_2(A_i)$.
--
--   The measure-theoretic data are: measurable spaces $V_i$; maps $\kappa_i : \mathrm{GL}_2(A_i) \to V_i$ and $\kappa'_i : \mathrm{GL}_2(L \otimes_K A_i) \to V_i$ which are measurable for the Borel $\sigma$-algebras `glBorelOf` of the two general linear groups and injective (`hκ`, `hκi`, `hκ'`, `hκ'i`); $\sigma$-finite reference measures $m_i$ on $V_i$ and $\delta$-dependent $\sigma$-finite reference measures $m'_i(\delta)$ (`hm`, `hm'`); complex numbers $\lambda_i$ indexed by $\iota$; Haar measures $\mu_i$ on $\mathrm{GL}_2(A_i)$ which are in addition right invariant (`hμ`, `hμr`); and Haar measures $\mu'_i$ on $\mathrm{GL}_2(L \otimes_K A_i)$ (`hμ'`), all for the Borel $\sigma$-algebras.
--
--   Throughout, $\gamma$ is called regular semisimple when $\mathrm{tr}(\gamma)^2 - 4\det(\gamma)$ is a unit; $\sigma_{\mathrm{GL}}$ denotes the automorphism of $\mathrm{GL}_2(L \otimes_K A_i)$ induced by $\sigma$ on the tensor factor, $\mathrm{Nm}(\delta) = \delta \cdot \sigma_{\mathrm{GL}}(\delta) \cdots \sigma_{\mathrm{GL}}^{[L:K]-1}(\delta)$ is the norm string, the twisted centraliser of $\delta$ is the subgroup $\{t : t\,\delta\,\sigma_{\mathrm{GL}}(t)^{-1} = \delta\}$, and $y$ is a norm conjugator for $(\gamma,\delta)$ when the image of $\gamma$ under $A_i \to L \otimes_K A_i$ satisfies $\gamma = y^{-1}\,\mathrm{Nm}(\delta)\,y$ in $\mathrm{GL}_2(L \otimes_K A_i)$.
--
--   The hypotheses fall into four groups.
--
--   (i) One-place untwisted section existence `hsecK`: for every $i$, every regular semisimple $\gamma \in \mathrm{GL}_2(A_i)$, every Haar measure $\tau$ on the centraliser of $\{\gamma\}$ and every continuous compactly supported $f : \mathrm{GL}_2(A_i) \to \mathbb{C}$ there is a continuous $w$ which is a section function for $(\gamma,\tau,f)$, i.e. $w \ge 0$, measurable, compactly supported, and $\int w(tx)\,d\tau(t) = 1$ for every $x$ with $f(x^{-1}\gamma x) \ne 0$.
--
--   (ii) One-place twisted section existence `hsecL`: for every $i$, every $\delta$, and every Haar, inversion-invariant measure $\tau'$ on the twisted centraliser of $\delta$, under the alternative that either $\mathrm{Nm}(\delta)$ is regular semisimple, or there exist a Haar measure $\tau$ on the centraliser of $\{\mathrm{scalar}(c_i)\}$ and a nonzero $s \in \mathbb{R}_{\ge 0}$ with $(\kappa_i)_*\tau = s \cdot m_i$ and $(\kappa'_i)_*\tau' = s \cdot m'_i(\delta)$, every continuous compactly supported $\varphi$ admits a continuous twisted section function $W$ for $(\delta,\tau',\varphi)$, i.e. $W \ge 0$, measurable, compactly supported, and $\int W(tx)\,d\tau'(t) = 1$ for every $x$ with $\varphi(x^{-1}\delta\,\sigma_{\mathrm{GL}}(x)) \ne 0$.
--
--   (iii) One-place central comparison `heng`: for every $i$, every $\varphi$ of the form $\Phi_1 \circ \varepsilon^L_i$ with $\Phi_1$ smooth on $Y_i$ and $\varphi$ compactly supported, and every $f$ of the form $F_1 \circ \varepsilon^K_i$ with $F_1$ smooth on $X_i$ and $f$ compactly supported: if there is a neighbourhood $V$ of $\mathrm{scalar}(c_i)$ such that for all $\delta$ with $\mathrm{Nm}(\delta)$ regular semisimple, all regular semisimple $\gamma \in V$, all norm conjugators $y$ for $(\gamma,\delta)$ and all Haar measures $\tau$, $\tau'$ on the centraliser of $\{\gamma\}$ and the twisted centraliser of $\delta$ which are coupled (the pushforward of $\tau'$ along $t \mapsto y^{-1}ty$ equals the pushforward of $\tau$ along the map induced by $A_i \to L \otimes_K A_i$), any twisted orbital integral value $I'$ of $\varphi$ at $\delta$ with respect to $\mu'_i$, $\tau'$ and any orbital integral value $I$ of $f$ at $\gamma$ with respect to $\mu_i$, $\tau$ agree, then: for all $\delta$ and all norm conjugators $y$ for $(\mathrm{scalar}(c_i),\delta)$, all Haar $\tau$ on the centraliser of $\{\mathrm{scalar}(c_i)\}$ and all Haar, inversion-invariant $\tau'$ on the twisted centraliser of $\delta$ for which there exists a nonzero $s \in \mathbb{R}_{\ge 0}$ with $(\kappa_i)_*\tau = s \cdot m_i$ and $(\kappa'_i)_*\tau' = s \cdot m'_i(\delta)$, and all $I, I' \in \mathbb{C}$ with $I'$ a twisted orbital integral value of $\varphi$ at $\delta$ and $I$ an orbital integral value of $f$ at $\mathrm{scalar}(c_i)$, one has $I' = \lambda_i \cdot I$.
--
--   (iv) Product data and product regular matching: $\nu$ is a Haar measure on $\prod_i \mathrm{GL}_2(A_i)$ and $\nu'$ a Haar measure on $\prod_i \mathrm{GL}_2(L \otimes_K A_i)$, both for the Borel $\sigma$-algebras; $F$ on the first product factors as a smooth function of the coordinates $\varepsilon^K_i(g_i)$ and has compact support (`hF`), and $\Phi$ on the second product factors as a smooth function of the coordinates $\varepsilon^L_i(g_i)$ and has compact support (`hΦ`). Writing $\Sigma$ for the product automorphism $(\sigma_{\mathrm{GL}})_i$ of $\prod_i \mathrm{GL}_2(L \otimes_K A_i)$, the hypothesis `hreg` requires: for all $\gamma$, $\delta$, $y$ in the respective products with every $\gamma_i$ regular semisimple, every $\mathrm{Nm}(\delta_i)$ regular semisimple and every $y_i$ a norm conjugator for $(\gamma_i,\delta_i)$, and for all Haar $\tau$ on the centraliser of $\{\gamma\}$ in the product group and Haar, inversion-invariant $\tau'$ on the $\Sigma$-twisted centraliser $\{t : t\,\delta\,\Sigma(t)^{-1} = \delta\}$ of $\delta$, such that the pushforward of $\tau'$ along $t \mapsto y^{-1}ty$ equals the pushforward of $\tau$ along $s \mapsto (s_i \otimes 1)_i$, the following holds for all $I, I' \in \mathbb{C}$: if there is $W \ge 0$, Borel measurable, compactly supported, with $\int W(tx)\,d\tau'(t) = 1$ whenever $\Phi(x^{-1}\delta\,\Sigma(x)) \ne 0$ and $I' = \int \Phi(x^{-1}\delta\,\Sigma(x))\,W(x)\,d\nu'(x)$, and there is $w \ge 0$, Borel measurable, compactly supported, with $\int w(sx)\,d\tau(s) = 1$ whenever $F(x^{-1}\gamma x) \ne 0$ and $I = \int F(x^{-1}\gamma x)\,w(x)\,d\nu(x)$, then $I' = I$.
--
--   Conclusion. Let $\gamma_0 = (\mathrm{scalar}(c_i))_{i}$ be the central element of $\prod_i \mathrm{GL}_2(A_i)$. For all $\delta$, $y$ in $\prod_i \mathrm{GL}_2(L \otimes_K A_i)$ such that for every $i$ the element $y_i$ is a norm conjugator for $(\mathrm{scalar}(c_i),\delta_i)$, for every Haar measure $\tau$ on the centraliser of $\{\gamma_0\}$ and every Haar, inversion-invariant measure $\tau'$ on the $\Sigma$-twisted centraliser of $\delta$ (Borel $\sigma$-algebras), if there exists a nonzero $s \in \mathbb{R}_{\ge 0}$ such that the pushforward of $\tau$ along $t \mapsto (\kappa_i(t_i))_i$ equals $s \cdot \bigotimes_i m_i$ and the pushforward of $\tau'$ along $t \mapsto (\kappa'_i(t_i))_i$ equals $s \cdot \bigotimes_i m'_i(\delta_i)$, both as measures on $\prod_i V_i$ with the product $\sigma$-algebra, then for all $I, I' \in \mathbb{C}$ the following implication holds: if there exists $W : \prod_i \mathrm{GL}_2(L \otimes_K A_i) \to \mathbb{R}$ with $W \ge 0$, Borel measurable, of compact support, satisfying $\int W(tx)\,d\tau'(t) = 1$ for every $x$ with $\Phi(x^{-1}\delta\,\Sigma(x)) \ne 0$, and $I' = \int \Phi(x^{-1}\delta\,\Sigma(x))\,W(x)\,d\nu'(x)$; and there exists $w : \prod_i \mathrm{GL}_2(A_i) \to \mathbb{R}$ with $w \ge 0$, Borel measurable, of compact support, satisfying $\int w(sx)\,d\tau(s) = 1$ for every $x$ with $F(x^{-1}\gamma_0 x) \ne 0$, and $I = \int F(x^{-1}\gamma_0 x)\,w(x)\,d\nu(x)$; then
--   $$I' = \Bigl(\prod_{i} \lambda_i\Bigr)\, I.$$
--   The conclusion thus compares the global twisted orbital integral of $\Phi$ at $\delta$ with the global orbital integral of $F$ at the central element $\gamma_0$, up to the product of the per-index factors $\lambda_i$; the two orbital integrals are written out explicitly rather than through the one-place predicates.
--
--   This is the semi-local (product over a finite set of places) form of the central transfer identity in base change for $\mathrm{GL}_2$, in a version where the torus measures at the central class are normalised against fixed reference measures $m_i$, $m'_i(\delta)$ by a single common scalar, and where each index contributes a factor $\lambda_i$. It is obtained from the one-index comparison by induction over $\iota$, via the peel step [`AutomorphicForm.semilocal_central_transfer_referenceMeasures_peel_step`](thm.html#AutomorphicForm.semilocal_central_transfer_referenceMeasures_peel_step), and is used in the archimedean assembly [`AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom`](thm.html#AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom), where the reference measures are Gram measures and $\lambda_i = -1$ at the relevant places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_semilocal_central_transfer_of_forall_oneplace_of_referenceMeasures.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions NNReal

theorem AutomorphicForm.semilocal_central_transfer_of_forall_oneplace_of_referenceMeasures
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (σ : L ≃ₐ[K] L)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, TopologicalSpace (A i)]
    [∀ i, IsTopologicalRing (A i)] [∀ i, T2Space (A i)] [∀ i, LocallyCompactSpace (A i)]
    [∀ i, SecondCountableTopology (A i)]
    (X Y : ι → Type) [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℝ (X i)] [∀ i, FiniteDimensional ℝ (X i)]
    [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace ℝ (Y i)] [∀ i, FiniteDimensional ℝ (Y i)]
    (εK : ∀ i, GL (Fin 2) (A i) → X i) (hεK : ∀ i, Continuous (εK i))
    (εL : ∀ i, GL (Fin 2) (L ⊗[K] A i) → Y i) (hεL : ∀ i, Continuous (εL i))
    (c : ∀ i, (A i)ˣ)

    (V : ι → Type) [∀ i, MeasurableSpace (V i)]
    (κ : ∀ i, GL (Fin 2) (A i) → V i) (hκ : ∀ i, Measurable[glBorelOf (A i)] (κ i)) (hκi : ∀ i, Function.Injective (κ i))
    (κ' : ∀ i, GL (Fin 2) (L ⊗[K] A i) → V i) (hκ' : ∀ i, Measurable[glBorelOf (L ⊗[K] A i)] (κ' i))
    (hκ'i : ∀ i, Function.Injective (κ' i))
    (m : ∀ i, Measure (V i)) (hm : ∀ i, SigmaFinite (m i))
    (m' : ∀ i, GL (Fin 2) (L ⊗[K] A i) → Measure (V i)) (hm' : ∀ i δ, SigmaFinite (m' i δ))
    (lam : ι → ℂ)
    (μ : ∀ i, @Measure (GL (Fin 2) (A i)) (glBorelOf (A i)))
    (hμ : ∀ i, @Measure.IsHaarMeasure _ _ _ (glBorelOf (A i)) (μ i))
    (hμr : ∀ i, @Measure.IsMulRightInvariant _ (glBorelOf (A i)) _ (μ i))
    (μ' : ∀ i, @Measure (GL (Fin 2) (L ⊗[K] A i)) (glBorelOf (L ⊗[K] A i)))
    (hμ' : ∀ i, @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] A i)) (μ' i))

    (hsecK : ∀ (i : ι) (γ : GL (Fin 2) (A i)), IsRegularSemisimple γ →
      ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (A i)))) (centralizerBorel (A i) γ),
        @Measure.IsHaarMeasure _ _ _ (centralizerBorel (A i) γ) τ →
      ∀ f : GL (Fin 2) (A i) → ℂ, Continuous f → HasCompactSupport f →
        ∃ w : GL (Fin 2) (A i) → ℝ, IsSectionFnOn (A i) γ τ f w ∧ Continuous w)
    (hsecL : ∀ (i : ι) (δ : GL (Fin 2) (L ⊗[K] A i)),
      ∀ τ' : @Measure (twistedCentralizer K L (A i) σ δ) (twistedCentralizerBorel K L (A i) σ δ),
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (A i) σ δ) τ' →
        @Measure.IsInvInvariant _ (twistedCentralizerBorel K L (A i) σ δ) _ τ' →
      (IsRegularSemisimple (normString K L (A i) σ δ) ∨
        ∃ (τ : @Measure (Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)} : Set (GL (Fin 2) (A i))))
              (centralizerBorel (A i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)))),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel (A i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i))) τ ∧
          (∃ s : ℝ≥0, s ≠ 0 ∧
            @Measure.map _ _ (centralizerBorel (A i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i))) _
                (fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)} : Set (GL (Fin 2) (A i))) => κ i (t : GL (Fin 2) (A i))) τ =
              s • m i ∧
            @Measure.map _ _ (twistedCentralizerBorel K L (A i) σ δ) _
                (fun t : twistedCentralizer K L (A i) σ δ => κ' i (t : GL (Fin 2) (L ⊗[K] A i))) τ' =
              s • m' i δ)) →
      ∀ φ : GL (Fin 2) (L ⊗[K] A i) → ℂ, Continuous φ → HasCompactSupport φ →
        ∃ W : GL (Fin 2) (L ⊗[K] A i) → ℝ, IsTwistedSectionFnOn K L (A i) σ δ τ' φ W ∧ Continuous W)

    (heng : ∀ (i : ι) (φ : GL (Fin 2) (L ⊗[K] A i) → ℂ),
      ((∃ Φ₁ : Y i → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ ∀ g, φ g = Φ₁ (εL i g)) ∧ HasCompactSupport φ) →
      ∀ (f : GL (Fin 2) (A i) → ℂ),
      ((∃ F₁ : X i → ℂ, ContDiff ℝ (⊤ : ℕ∞) F₁ ∧ ∀ g, f g = F₁ (εK i g)) ∧ HasCompactSupport f) →
      (∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)),
        ∀ δ : GL (Fin 2) (L ⊗[K] A i), IsRegularSemisimple (normString K L (A i) σ δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (L ⊗[K] A i), IsNormConjugator K L (A i) σ γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (A i)))) (centralizerBorel (A i) γ))
          (τ' : @Measure (twistedCentralizer K L (A i) σ δ) (twistedCentralizerBorel K L (A i) σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel (A i) γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (A i) σ δ) τ' →
          Coupled K L (A i) σ γ δ y τ τ' →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L (A i) σ (μ' i) δ τ' φ I' →
            IsOrbitalIntegralOn (A i) (μ i) γ τ f I → I' = I) →
      ∀ δ y : GL (Fin 2) (L ⊗[K] A i),
        IsNormConjugator K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) δ y →
        ∀ (τ : @Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)} : Set (GL (Fin 2) (A i))))
              (centralizerBorel (A i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i))))
          (τ' : @Measure (twistedCentralizer K L (A i) σ δ) (twistedCentralizerBorel K L (A i) σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel (A i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i))) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (A i) σ δ) τ' →
          @Measure.IsInvInvariant _ (twistedCentralizerBorel K L (A i) σ δ) _ τ' →
          (∃ s : ℝ≥0, s ≠ 0 ∧
            @Measure.map _ _ (centralizerBorel (A i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i))) _
                (fun t : Subgroup.centralizer ({Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)} : Set (GL (Fin 2) (A i))) => κ i (t : GL (Fin 2) (A i))) τ =
              s • m i ∧
            @Measure.map _ _ (twistedCentralizerBorel K L (A i) σ δ) _
                (fun t : twistedCentralizer K L (A i) σ δ => κ' i (t : GL (Fin 2) (L ⊗[K] A i))) τ' =
              s • m' i δ) →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L (A i) σ (μ' i) δ τ' φ I' →
            IsOrbitalIntegralOn (A i) (μ i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) τ f I → I' = lam i * I)

    (ν : @Measure ((i : ι) → GL (Fin 2) (A i)) (borel _)) (hν : @Measure.IsHaarMeasure ((i : ι) → GL (Fin 2) (A i)) _ _ (borel _) ν)
    (ν' : @Measure ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) (borel _)) (hν' : @Measure.IsHaarMeasure ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) _ _ (borel _) ν')
    (F : ((i : ι) → GL (Fin 2) (A i)) → ℂ)
    (hF : (∃ F₁ : ((i : ι) → X i) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F₁ ∧ ∀ g, F g = F₁ (fun i => εK i (g i))) ∧
      HasCompactSupport F)
    (Φ : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) → ℂ)
    (hΦ : (∃ Φ₁ : ((i : ι) → Y i) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ ∀ g, Φ g = Φ₁ (fun i => εL i (g i))) ∧
      HasCompactSupport Φ)

    (hreg : ∀ (γ : ((i : ι) → GL (Fin 2) (A i))) (δ y : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))),
      (∀ i, IsRegularSemisimple (γ i)) → (∀ i, IsRegularSemisimple (normString K L (A i) σ (δ i))) →
      (∀ i, IsNormConjugator K L (A i) σ (γ i) (δ i) (y i)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set ((i : ι) → GL (Fin 2) (A i)))) (borel _))
        (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
        @Measure.IsHaarMeasure _ _ _ (borel _) τ → @Measure.IsHaarMeasure _ _ _ (borel _) τ' →
        @Measure.IsInvInvariant _ (borel _) _ τ' →
        @Measure.map _ _ (borel _) (borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i)))
            (fun t : sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ => y⁻¹ * (t : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) * y) τ' =
          @Measure.map _ _ (borel _) (borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i)))
            (fun s : Subgroup.centralizer ({γ} : Set ((i : ι) → GL (Fin 2) (A i))) => fun i => toTensorGL K L (A i) ((s : ((i : ι) → GL (Fin 2) (A i))) i)) τ →
        ∀ I I' : ℂ,
          (∃ W : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, (∀ x, 0 ≤ W x) ∧ Measurable[borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i))] W ∧ HasCompactSupport W ∧
            (∀ x : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)), Φ (x⁻¹ * δ * (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
            I' = @integral _ ℂ _ _ (borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) ν' (fun x => Φ (x⁻¹ * δ * (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) x) * (W x : ℂ))) →
          (∃ w : ((i : ι) → GL (Fin 2) (A i)) → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable[borel ((i : ι) → GL (Fin 2) (A i))] w ∧ HasCompactSupport w ∧
            (∀ x : ((i : ι) → GL (Fin 2) (A i)), F (x⁻¹ * γ * x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : ((i : ι) → GL (Fin 2) (A i))) * x)) = 1) ∧
            I = @integral _ ℂ _ _ (borel ((i : ι) → GL (Fin 2) (A i))) ν (fun x => F (x⁻¹ * γ * x) * (w x : ℂ))) →
          I' = I) :

    ∀ (δ y : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))),
      (∀ i, IsNormConjugator K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) (δ i) (y i)) →
      ∀ (τ : @Measure (Subgroup.centralizer
            ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : ι) → GL (Fin 2) (A i)))} : Set ((i : ι) → GL (Fin 2) (A i)))) (borel _))
        (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
        @Measure.IsHaarMeasure _ _ _ (borel _) τ → @Measure.IsHaarMeasure _ _ _ (borel _) τ' →
        @Measure.IsInvInvariant _ (borel _) _ τ' →
        (∃ s : ℝ≥0, s ≠ 0 ∧
          @Measure.map _ _ (borel _) MeasurableSpace.pi
              (fun t : Subgroup.centralizer ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : ι) → GL (Fin 2) (A i)))} : Set ((i : ι) → GL (Fin 2) (A i))) =>
                fun i => κ i ((t : ((i : ι) → GL (Fin 2) (A i))) i)) τ =
            s • Measure.pi m ∧
          @Measure.map _ _ (borel _) MeasurableSpace.pi
              (fun t : sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ => fun i => κ' i ((t : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) i)) τ' =
            s • Measure.pi (fun i => m' i (δ i))) →
        ∀ I I' : ℂ,
          (∃ W : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, (∀ x, 0 ≤ W x) ∧ Measurable[borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i))] W ∧ HasCompactSupport W ∧
            (∀ x : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)), Φ (x⁻¹ * δ * (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
            I' = @integral _ ℂ _ _ (borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) ν' (fun x => Φ (x⁻¹ * δ * (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) x) * (W x : ℂ))) →
          (∃ w : ((i : ι) → GL (Fin 2) (A i)) → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable[borel ((i : ι) → GL (Fin 2) (A i))] w ∧ HasCompactSupport w ∧
            (∀ x : ((i : ι) → GL (Fin 2) (A i)), F (x⁻¹ * (fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) * x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : ((i : ι) → GL (Fin 2) (A i))) * x)) = 1) ∧
            I = @integral _ ℂ _ _ (borel ((i : ι) → GL (Fin 2) (A i))) ν
              (fun x => F (x⁻¹ * (fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) * x) * (w x : ℂ))) →
          I' = (∏ i, lam i) * I := by sorry
