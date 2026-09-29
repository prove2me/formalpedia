-- Prove2me | Theorems.Thm_AutomorphicForm_semilocal_central_transfer_of_forall_oneplace_of_isInvInvariant
-- name    : AutomorphicForm.semilocal_central_transfer_of_forall_oneplace_of_isInvInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/d821ba61-5e97-5193-8064-0aa20ace67aa
-- title:
--   Semi-local central transfer from one-place central comparisons
-- statement:
--   Fix fields $K$ and $L$ with $L$ a finite-dimensional $K$-algebra, and a $K$-algebra automorphism $\sigma$ of $L$. Fix a finite index type $\iota$ and, for each $i \in \iota$, a commutative topological $K$-algebra $A_i$ which is Hausdorff, locally compact and second countable, together with finite-dimensional real normed spaces $X_i$ and $Y_i$, continuous coordinate maps $\varepsilon^K_i : \mathrm{GL}_2(A_i) \to X_i$ and $\varepsilon^L_i : \mathrm{GL}_2(L \otimes_K A_i) \to Y_i$, and a unit $c_i \in A_i^{\times}$. All groups $\mathrm{GL}_2(A_i)$, $\mathrm{GL}_2(L \otimes_K A_i)$, their centralisers and the corresponding products carry their Borel $\sigma$-algebras. The measure data are: a Haar measure $\mu_i$ on $\mathrm{GL}_2(A_i)$ which is in addition right invariant (`hμ`, `hμr`), and a Haar measure $\mu'_i$ on $\mathrm{GL}_2(L \otimes_K A_i)$ (`hμ'`).
--
--   Throughout, $\gamma \in \mathrm{GL}_2(A_i)$ is *regular semisimple* in the sense of `IsRegularSemisimple`, i.e. $(\operatorname{tr}\gamma)^2 - 4\det\gamma$ is a unit; `sigmaGL` denotes the automorphism of $\mathrm{GL}_2(L \otimes_K A_i)$ obtained by applying $\sigma \otimes \mathrm{id}$ entrywise, written $\sigma$ below; `normString` is the norm string $\delta \cdot \sigma(\delta) \cdots \sigma^{n-1}(\delta)$ with $n = \operatorname{finrank}_K L$; `toTensorGL` is the map $\mathrm{GL}_2(A_i) \to \mathrm{GL}_2(L \otimes_K A_i)$ induced by $a \mapsto 1 \otimes a$; the twisted centraliser of $\delta$ is the subgroup $\{t : t\,\delta\,\sigma(t)^{-1} = \delta\}$; and `IsNormConjugator K L (A i) σ γ δ y` asserts $\mathrm{toTensorGL}(\gamma) = y^{-1}\,\mathrm{normString}(\delta)\,y$.
--
--   The hypotheses are grouped as follows.
--
--   `hsecK` (one-place untwisted section existence): for each $i$, each regular semisimple $\gamma \in \mathrm{GL}_2(A_i)$, each Haar measure $\tau$ on the centraliser of $\gamma$, and each continuous compactly supported $f : \mathrm{GL}_2(A_i) \to \mathbb{C}$, there is a continuous $w$ which is nonnegative, measurable, compactly supported and satisfies $\int_{Z(\gamma)} w(tx)\,\mathrm{d}\tau = 1$ for every $x$ with $f(x^{-1}\gamma x) \neq 0$.
--
--   `hsecL` (one-place twisted section existence): for each $i$ and each $\delta \in \mathrm{GL}_2(L \otimes_K A_i)$ such that either $\mathrm{normString}(\delta)$ is regular semisimple or $\delta$ is $\sigma$-conjugate to a scalar matrix $\mathrm{scalar}(d)$ for some $d \in (L \otimes_K A_i)^{\times}$ (that is, $\mathrm{scalar}(d) = x^{-1}\delta\,\sigma(x)$ for some $x$), for each Haar measure $\tau'$ on the twisted centraliser of $\delta$ which is also inversion invariant, and each continuous compactly supported $\varphi$, there is a continuous $W$ which is nonnegative, measurable, compactly supported and satisfies $\int W(tx)\,\mathrm{d}\tau' = 1$ for every $x$ with $\varphi(x^{-1}\delta\,\sigma(x)) \neq 0$.
--
--   `heng` (the one-place central comparison engine): for each $i$, each $\varphi$ of the form $\Phi_1 \circ \varepsilon^L_i$ with $\Phi_1$ smooth on $Y_i$ and $\varphi$ compactly supported, and each $f$ of the form $F_1 \circ \varepsilon^K_i$ with $F_1$ smooth on $X_i$ and $f$ compactly supported, the following implication holds. Suppose there is a neighbourhood $V$ of $\mathrm{scalar}(c_i)$ such that for all $\delta$ with $\mathrm{normString}(\delta)$ regular semisimple, all regular semisimple $\gamma \in V$, all $y$ with $\mathrm{toTensorGL}(\gamma) = y^{-1}\mathrm{normString}(\delta)y$, all Haar measures $\tau$ on the centraliser of $\gamma$ and $\tau'$ on the twisted centraliser of $\delta$ which are coupled in the sense of `Coupled` (the image of $\tau'$ under $t \mapsto y^{-1}ty$ equals the image of $\tau$ under `toTensorGL`), and all $I, I' \in \mathbb{C}$ with $I'$ a twisted orbital integral of $\varphi$ at $\delta$ relative to $\mu'_i$ and $\tau'$ and $I$ an orbital integral of $f$ at $\gamma$ relative to $\mu_i$ and $\tau$, one has $I' = I$. Then the same equality holds at the central element: for all $\delta, y$ with $\mathrm{toTensorGL}(\mathrm{scalar}(c_i)) = y^{-1}\mathrm{normString}(\delta)y$, all Haar $\tau$ on the centraliser of $\mathrm{scalar}(c_i)$ and all Haar, inversion invariant $\tau'$ on the twisted centraliser of $\delta$ which are coupled, and all $I, I'$ with $I'$ a twisted orbital integral of $\varphi$ at $\delta$ and $I$ an orbital integral of $f$ at $\mathrm{scalar}(c_i)$, one has $I' = I$.
--
--   Global data: Haar measures $\nu$ on $\prod_i \mathrm{GL}_2(A_i)$ and $\nu'$ on $\prod_i \mathrm{GL}_2(L \otimes_K A_i)$; a function $F$ on $\prod_i \mathrm{GL}_2(A_i)$ which by `hF` is of the form $F_1\bigl((\varepsilon^K_i(g_i))_i\bigr)$ with $F_1$ smooth on $\prod_i X_i$ and has compact support; a function $\Phi$ on $\prod_i \mathrm{GL}_2(L \otimes_K A_i)$ which by `hΦ` is of the form $\Phi_1\bigl((\varepsilon^L_i(g_i))_i\bigr)$ with $\Phi_1$ smooth on $\prod_i Y_i$ and has compact support. On the product $\prod_i \mathrm{GL}_2(L \otimes_K A_i)$ the twist is the componentwise map $x \mapsto (\sigma(x_i))_i$, and `sigmaCentralizer` of $\delta$ for this map is $\{t : t\,\delta\,\sigma(t)^{-1} = \delta\}$.
--
--   `hreg` (global matching at regular classes): for all $\gamma \in \prod_i \mathrm{GL}_2(A_i)$ and $\delta, y \in \prod_i \mathrm{GL}_2(L \otimes_K A_i)$ such that every $\gamma_i$ is regular semisimple, every $\mathrm{normString}(\delta_i)$ is regular semisimple and $\mathrm{toTensorGL}(\gamma_i) = y_i^{-1}\mathrm{normString}(\delta_i)y_i$ for every $i$, for all Haar measures $\tau$ on the centraliser of $\gamma$ in the product group and $\tau'$ on the product $\sigma$-centraliser of $\delta$ with $\tau'$ inversion invariant, such that the image of $\tau'$ under $t \mapsto y^{-1}ty$ equals the image of $\tau$ under $s \mapsto (\mathrm{toTensorGL}(s_i))_i$, and for all $I, I' \in \mathbb{C}$: if there exists $W$ on $\prod_i \mathrm{GL}_2(L \otimes_K A_i)$ which is nonnegative, Borel measurable, compactly supported, satisfies $\int W(tx)\,\mathrm{d}\tau' = 1$ for every $x$ with $\Phi(x^{-1}\delta\,\sigma(x)) \neq 0$, and with $I' = \int \Phi(x^{-1}\delta\,\sigma(x))\,W(x)\,\mathrm{d}\nu'$, and if there exists $w$ on $\prod_i \mathrm{GL}_2(A_i)$ which is nonnegative, Borel measurable, compactly supported, satisfies $\int w(sx)\,\mathrm{d}\tau = 1$ for every $x$ with $F(x^{-1}\gamma x) \neq 0$, and with $I = \int F(x^{-1}\gamma x)\,w(x)\,\mathrm{d}\nu$, then $I' = I$.
--
--   Under these hypotheses the conclusion is the corresponding identity at the central class $\gamma = (\mathrm{scalar}(c_i))_i$: for all $\delta, y \in \prod_i \mathrm{GL}_2(L \otimes_K A_i)$ such that $\mathrm{toTensorGL}(\mathrm{scalar}(c_i)) = y_i^{-1}\mathrm{normString}(\delta_i)y_i$ for every $i$, for every Haar measure $\tau$ on the centraliser of $(\mathrm{scalar}(c_i))_i$ in $\prod_i \mathrm{GL}_2(A_i)$ and every Haar, inversion invariant measure $\tau'$ on the product $\sigma$-centraliser of $\delta$, such that the image of $\tau'$ under $t \mapsto y^{-1}ty$ equals the image of $\tau$ under $s \mapsto (\mathrm{toTensorGL}(s_i))_i$, and for all $I, I' \in \mathbb{C}$, the following implication holds. If there exists a nonnegative, Borel measurable, compactly supported $W$ with $\int W(tx)\,\mathrm{d}\tau' = 1$ whenever $\Phi(x^{-1}\delta\,\sigma(x)) \neq 0$ and $I' = \int \Phi(x^{-1}\delta\,\sigma(x))\,W(x)\,\mathrm{d}\nu'$, and there exists a nonnegative, Borel measurable, compactly supported $w$ with $\int w(sx)\,\mathrm{d}\tau = 1$ whenever $F\bigl(x^{-1}(\mathrm{scalar}(c_i))_i\,x\bigr) \neq 0$ and $I = \int F\bigl(x^{-1}(\mathrm{scalar}(c_i))_i\,x\bigr)\,w(x)\,\mathrm{d}\nu$, then $I' = I$.
--
--   This is the semi-local form of the central case of base-change transfer for $\mathrm{GL}_2$: matching of orbital and twisted orbital integrals at regular classes on a finite product of local factors, together with a comparison at each single factor near the scalar class, propagates to the identity at the central class of the product. It is obtained from the one-index version [`AutomorphicForm.semilocal_central_transfer_peel_step`](thm.html#AutomorphicForm.semilocal_central_transfer_peel_step), and it feeds the archimedean matching and central twisted-orbital-integral statements [`AutomorphicForm.areMatchingArch_central_transfer_of_scalar_of_forall_conjAe_of_forall_algHom`](thm.html#AutomorphicForm.areMatchingArch_central_transfer_of_scalar_of_forall_conjAe_of_forall_algHom) and [`AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom`](thm.html#AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_semilocal_central_transfer_of_forall_oneplace_of_isInvInvariant.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions NNReal

theorem AutomorphicForm.semilocal_central_transfer_of_forall_oneplace_of_isInvInvariant
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
      (IsRegularSemisimple (normString K L (A i) σ δ) ∨
        ∃ d : (L ⊗[K] A i)ˣ, IsSigmaConjugate K L (A i) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)) →
      ∀ τ' : @Measure (twistedCentralizer K L (A i) σ δ) (twistedCentralizerBorel K L (A i) σ δ),
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (A i) σ δ) τ' →
        @Measure.IsInvInvariant _ (twistedCentralizerBorel K L (A i) σ δ) _ τ' →
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
          Coupled K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) δ y τ τ' →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L (A i) σ (μ' i) δ τ' φ I' →
            IsOrbitalIntegralOn (A i) (μ i) (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) τ f I → I' = I)

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
        @Measure.map _ _ (borel _) (borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i)))
            (fun t : sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ => y⁻¹ * (t : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) * y) τ' =
          @Measure.map _ _ (borel _) (borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i)))
            (fun s : Subgroup.centralizer
                ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : ι) → GL (Fin 2) (A i)))} : Set ((i : ι) → GL (Fin 2) (A i))) =>
              fun i => toTensorGL K L (A i) ((s : ((i : ι) → GL (Fin 2) (A i))) i)) τ →
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
          I' = I := by sorry
