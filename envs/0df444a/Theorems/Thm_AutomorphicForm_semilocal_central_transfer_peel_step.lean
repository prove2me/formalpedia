-- Prove2me | Theorems.Thm_AutomorphicForm_semilocal_central_transfer_peel_step
-- name    : AutomorphicForm.semilocal_central_transfer_peel_step
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/3de44751-dfe8-5a7d-8373-6ef4c8ebbfb1
-- title:
--   Peel step for the semi-local central transfer
-- statement:
--   Throughout, $K \subseteq L$ is a finite extension of fields and $\sigma$ a $K$-algebra automorphism of $L$; $\iota$ is a finite index type and $A : \iota \to \mathrm{Type}$ a family of commutative $K$-algebras, each carrying a topology making it a Hausdorff, locally compact, second countable topological ring. Two families $X, Y$ of finite-dimensional real normed spaces are given, together with continuous "coordinate readings" $\varepsilon_K^i : \mathrm{GL}_2(A_i) \to X_i$ (continuity is the hypothesis `hεK`) and $\varepsilon_L^i : \mathrm{GL}_2(L \otimes_K A_i) \to Y_i$ (continuity is `hεL`), and units $c_i \in A_i^{\times}$. For each $i$ a measure $\mu_i$ on $\mathrm{GL}_2(A_i)$ is given which is Haar (`hμ`) and in addition right invariant (`hμr`), and a Haar measure $\mu'_i$ on $\mathrm{GL}_2(L \otimes_K A_i)$ (`hμ'`); all measures in the statement are taken with respect to the Borel $\sigma$-algebras attached to the relevant topologies (`glBorelOf`, `centralizerBorel`, `twistedCentralizerBorel`, and `borel` on products and their subgroups).
--
--   The notions used are the following. An element $g$ of $\mathrm{GL}_2(R)$ is regular semisimple (`IsRegularSemisimple`) when $\operatorname{tr}(g)^2 - 4\det(g)$ is a unit of $R$. The map `toTensorGL` is the base change $\mathrm{GL}_2(A) \to \mathrm{GL}_2(L \otimes_K A)$ induced by $a \mapsto 1 \otimes a$, and `sigmaGL` is the automorphism of $\mathrm{GL}_2(L \otimes_K A)$ induced by $\sigma \otimes \mathrm{id}_A$; it is written $\sigma$ below as well. The norm string of $\delta$ is $N\delta = \delta \cdot \sigma(\delta) \cdots \sigma^{n-1}(\delta)$ with $n = [L:K]$. Two elements are $\sigma$-conjugate (`IsSigmaConjugate`) when $\delta' = x^{-1}\delta\,\sigma(x)$ for some $x$; $y$ is a norm conjugator (`IsNormConjugator`) from $\gamma$ to $\delta$ when $1 \otimes \gamma = y^{-1} (N\delta) y$. For a monoid endomorphism $\theta$ of a group $G$, `sigmaCentralizer` $\theta\,\delta$ is the subgroup $\{t : t\delta\theta(t)^{-1} = \delta\}$; the twisted centralizer of $\delta$ is this subgroup for $\theta =$ `sigmaGL`. A pair $(\tau, \tau')$ of measures on the centralizer of $\gamma$ and on the twisted centralizer of $\delta$ is coupled through $y$ (`Coupled`) when the image of $\tau'$ under $t \mapsto y^{-1} t y$ equals the image of $\tau$ under base change. A section function for $(\gamma,\tau,f)$ (`IsSectionFnOn`) is a non-negative measurable compactly supported $w$ with $\int_{Z(\gamma)} w(tx)\,d\tau = 1$ for every $x$ with $f(x^{-1}\gamma x) \ne 0$; the twisted variant (`IsTwistedSectionFnOn`) replaces $x^{-1}\gamma x$ by $x^{-1}\delta\,\sigma(x)$ and $Z(\gamma)$ by the twisted centralizer. Orbital and twisted orbital integrals (`IsOrbitalIntegralOn`, `IsTwistedOrbitalIntegralOn`) assert that the given complex number equals $\int f(x^{-1}\gamma x) w(x)\,d\mu$, respectively $\int \varphi(x^{-1}\delta\,\sigma(x)) W(x)\,d\mu'$, for some (twisted) section function.
--
--   The one-place hypotheses are three. `hsecK`: for every $i$, every regular semisimple $\gamma \in \mathrm{GL}_2(A_i)$, every Haar measure $\tau$ on the centralizer of $\gamma$ and every continuous compactly supported $f : \mathrm{GL}_2(A_i) \to \mathbb{C}$, there is a continuous section function for $(\gamma, \tau, f)$. `hsecL`: for every $i$ and every $\delta \in \mathrm{GL}_2(L \otimes_K A_i)$ such that either $N\delta$ is regular semisimple or $\delta$ is $\sigma$-conjugate to a scalar matrix $\mathrm{scalar}(d)$ with $d \in (L \otimes_K A_i)^{\times}$, every Haar and inversion-invariant measure $\tau'$ on the twisted centralizer of $\delta$ and every continuous compactly supported $\varphi$, there is a continuous twisted section function for $(\delta, \tau', \varphi)$. `heng` is the one-place passage from regular semisimple matching to central matching: for every $i$, every compactly supported $\varphi$ of the form $\Phi_1 \circ \varepsilon_L^i$ with $\Phi_1$ smooth on $Y_i$, and every compactly supported $f$ of the form $F_1 \circ \varepsilon_K^i$ with $F_1$ smooth on $X_i$, if there is a neighbourhood $V$ of $\mathrm{scalar}(c_i)$ such that for all $\delta$ with $N\delta$ regular semisimple, all regular semisimple $\gamma \in V$, all norm conjugators $y$ from $\gamma$ to $\delta$, all Haar $\tau$ on the centralizer of $\gamma$ and Haar $\tau'$ on the twisted centralizer of $\delta$ coupled through $y$, and all $I, I' \in \mathbb{C}$ with $I'$ a twisted orbital integral of $\varphi$ at $\delta$ for $(\mu'_i, \tau')$ and $I$ an orbital integral of $f$ at $\gamma$ for $(\mu_i, \tau)$, one has $I' = I$, then the same equality $I' = I$ holds at the central element $\mathrm{scalar}(c_i)$: for all $\delta, y$ with $y$ a norm conjugator from $\mathrm{scalar}(c_i)$ to $\delta$, all Haar $\tau$ on the centralizer of $\mathrm{scalar}(c_i)$, all Haar and inversion-invariant $\tau'$ on the twisted centralizer of $\delta$ coupled through $y$, and all $I, I'$ given as the corresponding twisted orbital and orbital integrals.
--
--   On the products $\mathbf{G}_K = \prod_i \mathrm{GL}_2(A_i)$ and $\mathbf{G}_L = \prod_i \mathrm{GL}_2(L \otimes_K A_i)$, Haar measures $\nu$ and $\nu'$ are given, and test functions $F : \mathbf{G}_K \to \mathbb{C}$, $\Phi : \mathbf{G}_L \to \mathbb{C}$ which are compactly supported and factor as smooth functions of the coordinate readings, $F(g) = F_1((\varepsilon_K^i(g_i))_i)$ and $\Phi(g) = \Phi_1((\varepsilon_L^i(g_i))_i)$ with $F_1, \Phi_1$ smooth (hypotheses `hF`, `hΦ`). Write $\Theta$ for the componentwise twist on $\mathbf{G}_L$, that is the product homomorphism whose $i$-th component is `sigmaGL` applied to the $i$-th coordinate. The hypothesis `hreg` is the transfer identity on the product at componentwise regular data: for all $\gamma \in \mathbf{G}_K$ and $\delta, y \in \mathbf{G}_L$ with every $\gamma_i$ regular semisimple, every $N(\delta_i)$ regular semisimple and every $y_i$ a norm conjugator from $\gamma_i$ to $\delta_i$, for all Haar $\tau$ on the centralizer of $\gamma$ in $\mathbf{G}_K$ and all Haar, inversion-invariant $\tau'$ on the $\Theta$-twisted centralizer of $\delta$ such that the image of $\tau'$ under $t \mapsto y^{-1} t y$ equals the image of $\tau$ under the componentwise base change $s \mapsto (1 \otimes s_i)_i$, and for all $I, I' \in \mathbb{C}$: if there is a non-negative, Borel measurable, compactly supported $W$ on $\mathbf{G}_L$ with $\int_{\tau'} W(tx) = 1$ whenever $\Phi(x^{-1}\delta\,\Theta(x)) \ne 0$ and $I' = \int_{\mathbf{G}_L} \Phi(x^{-1}\delta\,\Theta(x)) W(x)\,d\nu'$, and there is a non-negative, Borel measurable, compactly supported $w$ on $\mathbf{G}_K$ with $\int_{\tau} w(sx) = 1$ whenever $F(x^{-1}\gamma x) \ne 0$ and $I = \int_{\mathbf{G}_K} F(x^{-1}\gamma x) w(x)\,d\nu$, then $I' = I$.
--
--   The induction hypothesis `ih` quantifies over an arbitrary finite index type $\kappa$ and an arbitrary package of data over $\kappa$ of exactly the shape just described — algebras $A_i$ with their topological hypotheses, normed spaces $X_i, Y_i$, continuous readings, units $c_i$, right-invariant Haar $\mu_i$ and Haar $\mu'_i$, the one-place hypotheses `hsecK`, `hsecL`, `heng`, Haar measures $\nu, \nu'$ on the two products, test functions $F, \Phi$ smooth through the readings and compactly supported, and the product identity `hreg` (these hypotheses are summarised here, the data over $\kappa$ being freshly quantified while $K$, $L$, $\sigma$ stay fixed) — and asserts that whenever $|\kappa| < |\iota|$ the four conjuncts below hold for that data over $\kappa$.
--
--   The conclusion is the conjunction of four statements over $\iota$, with $\mathbf{c} = (\mathrm{scalar}(c_i))_i \in \mathbf{G}_K$.
--
--   First, central matching on the product: for all $\delta, y \in \mathbf{G}_L$ such that each $y_i$ is a norm conjugator from $\mathrm{scalar}(c_i)$ to $\delta_i$, for all Haar $\tau$ on the centralizer of $\mathbf{c}$ in $\mathbf{G}_K$ and all Haar, inversion-invariant $\tau'$ on the $\Theta$-twisted centralizer of $\delta$ whose image under $t \mapsto y^{-1} t y$ equals the image of $\tau$ under componentwise base change, and for all $I, I' \in \mathbb{C}$: if there is a non-negative, Borel measurable, compactly supported $W$ on $\mathbf{G}_L$ satisfying $\int_{\tau'} W(tx) = 1$ for every $x$ with $\Phi(x^{-1}\delta\,\Theta(x)) \ne 0$ and $I' = \int_{\mathbf{G}_L} \Phi(x^{-1}\delta\,\Theta(x)) W(x)\,d\nu'$, and there is a non-negative, Borel measurable, compactly supported $w$ on $\mathbf{G}_K$ satisfying $\int_{\tau} w(sx) = 1$ for every $x$ with $F(x^{-1}\mathbf{c}\,x) \ne 0$ and $I = \int_{\mathbf{G}_K} F(x^{-1}\mathbf{c}\,x) w(x)\,d\nu$, then $I' = I$.
--
--   Second, twisted section functions at central data: for all $\delta, y$, $\tau$, $\tau'$ as in the first conjunct (same norm-conjugator, Haar, inversion-invariance and coupling conditions), and for every continuous compactly supported $\Psi : \mathbf{G}_L \to \mathbb{C}$, there exists a continuous, non-negative, compactly supported $W$ on $\mathbf{G}_L$ such that $\int_{\tau'} W(tx) = 1$ for every $x$ with $\Psi(x^{-1}\delta\,\Theta(x)) \ne 0$.
--
--   Third, twisted section functions at componentwise regular data: for every $\delta \in \mathbf{G}_L$ with each $N(\delta_i)$ regular semisimple, every Haar and inversion-invariant $\tau'$ on the $\Theta$-twisted centralizer of $\delta$ and every continuous compactly supported $\Psi$ on $\mathbf{G}_L$, there exists a continuous, non-negative, compactly supported $W$ with $\int_{\tau'} W(tx) = 1$ for every $x$ with $\Psi(x^{-1}\delta\,\Theta(x)) \ne 0$.
--
--   Fourth, ordinary section functions at componentwise regular data: for every $\gamma \in \mathbf{G}_K$ with each $\gamma_i$ regular semisimple, every Haar measure $\tau$ on the centralizer of $\gamma$ in $\mathbf{G}_K$ and every continuous compactly supported $\Psi$ on $\mathbf{G}_K$, there exists a continuous, non-negative, compactly supported $w$ with $\int_{\tau} w(sx) = 1$ for every $x$ with $\Psi(x^{-1}\gamma x) \ne 0$.
--
--   This is the induction step in the semi-local form of the central $\sigma$-twisted transfer identity for $\mathrm{GL}_2$ in a cyclic situation, of the kind underlying base change: the four assertions (central matching of twisted and ordinary orbital integrals on the product, plus existence of the normalising section functions) are propagated from all strictly shorter products of places to the product over $\iota$, one factor being peeled off and the one-place hypotheses `hsecK`, `hsecL`, `heng` applied there. It is consumed by [`AutomorphicForm.semilocal_central_transfer_of_forall_oneplace_of_isInvInvariant`](thm.html#AutomorphicForm.semilocal_central_transfer_of_forall_oneplace_of_isInvInvariant), whose proof is the strong induction on $|\iota|$ fed by this step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_semilocal_central_transfer_peel_step.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions NNReal

theorem AutomorphicForm.semilocal_central_transfer_peel_step
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
          I' = I)

    (ih : ∀ {κ : Type} [Fintype κ] [DecidableEq κ]
      (A : κ → Type) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, TopologicalSpace (A i)]
      [∀ i, IsTopologicalRing (A i)] [∀ i, T2Space (A i)] [∀ i, LocallyCompactSpace (A i)]
      [∀ i, SecondCountableTopology (A i)]
      (X Y : κ → Type) [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℝ (X i)] [∀ i, FiniteDimensional ℝ (X i)]
      [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace ℝ (Y i)] [∀ i, FiniteDimensional ℝ (Y i)]
      (εK : ∀ i, GL (Fin 2) (A i) → X i) (hεK : ∀ i, Continuous (εK i))
      (εL : ∀ i, GL (Fin 2) (L ⊗[K] A i) → Y i) (hεL : ∀ i, Continuous (εL i))
      (c : ∀ i, (A i)ˣ)
      (μ : ∀ i, @Measure (GL (Fin 2) (A i)) (glBorelOf (A i)))
      (hμ : ∀ i, @Measure.IsHaarMeasure _ _ _ (glBorelOf (A i)) (μ i))
      (hμr : ∀ i, @Measure.IsMulRightInvariant _ (glBorelOf (A i)) _ (μ i))
      (μ' : ∀ i, @Measure (GL (Fin 2) (L ⊗[K] A i)) (glBorelOf (L ⊗[K] A i)))
      (hμ' : ∀ i, @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] A i)) (μ' i))
      (hsecK : ∀ (i : κ) (γ : GL (Fin 2) (A i)), IsRegularSemisimple γ →
      ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (A i)))) (centralizerBorel (A i) γ),
      @Measure.IsHaarMeasure _ _ _ (centralizerBorel (A i) γ) τ →
      ∀ f : GL (Fin 2) (A i) → ℂ, Continuous f → HasCompactSupport f →
      ∃ w : GL (Fin 2) (A i) → ℝ, IsSectionFnOn (A i) γ τ f w ∧ Continuous w)
      (hsecL : ∀ (i : κ) (δ : GL (Fin 2) (L ⊗[K] A i)),
      (IsRegularSemisimple (normString K L (A i) σ δ) ∨
      ∃ d : (L ⊗[K] A i)ˣ, IsSigmaConjugate K L (A i) σ δ (Matrix.GeneralLinearGroup.scalar (Fin 2) d)) →
      ∀ τ' : @Measure (twistedCentralizer K L (A i) σ δ) (twistedCentralizerBorel K L (A i) σ δ),
      @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (A i) σ δ) τ' →
      @Measure.IsInvInvariant _ (twistedCentralizerBorel K L (A i) σ δ) _ τ' →
      ∀ φ : GL (Fin 2) (L ⊗[K] A i) → ℂ, Continuous φ → HasCompactSupport φ →
      ∃ W : GL (Fin 2) (L ⊗[K] A i) → ℝ, IsTwistedSectionFnOn K L (A i) σ δ τ' φ W ∧ Continuous W)
      (heng : ∀ (i : κ) (φ : GL (Fin 2) (L ⊗[K] A i) → ℂ),
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
      (ν : @Measure ((i : κ) → GL (Fin 2) (A i)) (borel _)) (hν : @Measure.IsHaarMeasure ((i : κ) → GL (Fin 2) (A i)) _ _ (borel _) ν)
      (ν' : @Measure ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) (borel _)) (hν' : @Measure.IsHaarMeasure ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) _ _ (borel _) ν')
      (F : ((i : κ) → GL (Fin 2) (A i)) → ℂ)
      (hF : (∃ F₁ : ((i : κ) → X i) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F₁ ∧ ∀ g, F g = F₁ (fun i => εK i (g i))) ∧
      HasCompactSupport F)
      (Φ : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) → ℂ)
      (hΦ : (∃ Φ₁ : ((i : κ) → Y i) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ ∀ g, Φ g = Φ₁ (fun i => εL i (g i))) ∧
      HasCompactSupport Φ)
      (hreg : ∀ (γ : ((i : κ) → GL (Fin 2) (A i))) (δ y : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))),
      (∀ i, IsRegularSemisimple (γ i)) → (∀ i, IsRegularSemisimple (normString K L (A i) σ (δ i))) →
      (∀ i, IsNormConjugator K L (A i) σ (γ i) (δ i) (y i)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set ((i : κ) → GL (Fin 2) (A i)))) (borel _))
      (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ → @Measure.IsHaarMeasure _ _ _ (borel _) τ' →
      @Measure.IsInvInvariant _ (borel _) _ τ' →
      @Measure.map _ _ (borel _) (borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i)))
      (fun t : sigmaCentralizer (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) δ => y⁻¹ * (t : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) * y) τ' =
      @Measure.map _ _ (borel _) (borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i)))
      (fun s : Subgroup.centralizer ({γ} : Set ((i : κ) → GL (Fin 2) (A i))) => fun i => toTensorGL K L (A i) ((s : ((i : κ) → GL (Fin 2) (A i))) i)) τ →
      ∀ I I' : ℂ,
      (∃ W : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, (∀ x, 0 ≤ W x) ∧ Measurable[borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i))] W ∧ HasCompactSupport W ∧
      (∀ x : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)), Φ (x⁻¹ * δ * (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
      I' = @integral _ ℂ _ _ (borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) ν' (fun x => Φ (x⁻¹ * δ * (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) x) * (W x : ℂ))) →
      (∃ w : ((i : κ) → GL (Fin 2) (A i)) → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable[borel ((i : κ) → GL (Fin 2) (A i))] w ∧ HasCompactSupport w ∧
      (∀ x : ((i : κ) → GL (Fin 2) (A i)), F (x⁻¹ * γ * x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : ((i : κ) → GL (Fin 2) (A i))) * x)) = 1) ∧
      I = @integral _ ℂ _ _ (borel ((i : κ) → GL (Fin 2) (A i))) ν (fun x => F (x⁻¹ * γ * x) * (w x : ℂ))) →
      I' = I),
      Fintype.card κ < Fintype.card ι →
      (∀ (δ y : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))),
      (∀ i, IsNormConjugator K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) (δ i) (y i)) →
      ∀ (τ : @Measure (Subgroup.centralizer
      ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : κ) → GL (Fin 2) (A i)))} : Set ((i : κ) → GL (Fin 2) (A i)))) (borel _))
      (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ → @Measure.IsHaarMeasure _ _ _ (borel _) τ' →
      @Measure.IsInvInvariant _ (borel _) _ τ' →
      @Measure.map _ _ (borel _) (borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i)))
      (fun t : sigmaCentralizer (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) δ => y⁻¹ * (t : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) * y) τ' =
      @Measure.map _ _ (borel _) (borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i)))
      (fun s : Subgroup.centralizer
      ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : κ) → GL (Fin 2) (A i)))} : Set ((i : κ) → GL (Fin 2) (A i))) =>
      fun i => toTensorGL K L (A i) ((s : ((i : κ) → GL (Fin 2) (A i))) i)) τ →
      ∀ I I' : ℂ,
      (∃ W : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, (∀ x, 0 ≤ W x) ∧ Measurable[borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i))] W ∧ HasCompactSupport W ∧
      (∀ x : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)), Φ (x⁻¹ * δ * (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
      I' = @integral _ ℂ _ _ (borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) ν' (fun x => Φ (x⁻¹ * δ * (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) x) * (W x : ℂ))) →
      (∃ w : ((i : κ) → GL (Fin 2) (A i)) → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable[borel ((i : κ) → GL (Fin 2) (A i))] w ∧ HasCompactSupport w ∧
      (∀ x : ((i : κ) → GL (Fin 2) (A i)), F (x⁻¹ * (fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) * x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : ((i : κ) → GL (Fin 2) (A i))) * x)) = 1) ∧
      I = @integral _ ℂ _ _ (borel ((i : κ) → GL (Fin 2) (A i))) ν
      (fun x => F (x⁻¹ * (fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) * x) * (w x : ℂ))) →
      I' = I) ∧
      (∀ (δ y : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))),
      (∀ i, IsNormConjugator K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) (δ i) (y i)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : κ) → GL (Fin 2) (A i)))} : Set ((i : κ) → GL (Fin 2) (A i)))) (borel _))
      (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ → @Measure.IsHaarMeasure _ _ _ (borel _) τ' →
      @Measure.IsInvInvariant _ (borel _) _ τ' →
      @Measure.map _ _ (borel _) (borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i)))
      (fun t : sigmaCentralizer (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) δ => y⁻¹ * (t : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) * y) τ' =
      @Measure.map _ _ (borel _) (borel ((i : κ) → GL (Fin 2) (L ⊗[K] A i)))
      (fun s : Subgroup.centralizer ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : κ) → GL (Fin 2) (A i)))} : Set ((i : κ) → GL (Fin 2) (A i))) =>
      fun i => toTensorGL K L (A i) ((s : ((i : κ) → GL (Fin 2) (A i))) i)) τ →
      ∀ Ψ : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
      ∃ W : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, Continuous W ∧ (∀ x, 0 ≤ W x) ∧ HasCompactSupport W ∧
      ∀ x : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)), Ψ (x⁻¹ * δ * (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
      (∀ (δ : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))), (∀ i, IsRegularSemisimple (normString K L (A i) σ (δ i))) →
      ∀ (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ' → @Measure.IsInvInvariant _ (borel _) _ τ' →
      ∀ Ψ : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
      ∃ W : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, Continuous W ∧ (∀ x, 0 ≤ W x) ∧ HasCompactSupport W ∧
      ∀ x : ((i : κ) → GL (Fin 2) (L ⊗[K] A i)), Ψ (x⁻¹ * δ * (MonoidHom.pi fun i : κ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : κ => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : κ) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
      (∀ (γ : ((i : κ) → GL (Fin 2) (A i))), (∀ i, IsRegularSemisimple (γ i)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set ((i : κ) → GL (Fin 2) (A i)))) (borel _)),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ →
      ∀ Ψ : ((i : κ) → GL (Fin 2) (A i)) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
      ∃ w : ((i : κ) → GL (Fin 2) (A i)) → ℝ, Continuous w ∧ (∀ x, 0 ≤ w x) ∧ HasCompactSupport w ∧
      ∀ x : ((i : κ) → GL (Fin 2) (A i)), Ψ (x⁻¹ * γ * x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : ((i : κ) → GL (Fin 2) (A i))) * x)) = 1)) :
    (∀ (δ y : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))),
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
          I' = I) ∧
    (∀ (δ y : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))),
      (∀ i, IsNormConjugator K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) (δ i) (y i)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : ι) → GL (Fin 2) (A i)))} : Set ((i : ι) → GL (Fin 2) (A i)))) (borel _))
        (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
        @Measure.IsHaarMeasure _ _ _ (borel _) τ → @Measure.IsHaarMeasure _ _ _ (borel _) τ' →
        @Measure.IsInvInvariant _ (borel _) _ τ' →
        @Measure.map _ _ (borel _) (borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i)))
            (fun t : sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ => y⁻¹ * (t : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) * y) τ' =
          @Measure.map _ _ (borel _) (borel ((i : ι) → GL (Fin 2) (L ⊗[K] A i)))
            (fun s : Subgroup.centralizer ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : ι) → GL (Fin 2) (A i)))} : Set ((i : ι) → GL (Fin 2) (A i))) =>
              fun i => toTensorGL K L (A i) ((s : ((i : ι) → GL (Fin 2) (A i))) i)) τ →
        ∀ Ψ : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
          ∃ W : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, Continuous W ∧ (∀ x, 0 ≤ W x) ∧ HasCompactSupport W ∧
            ∀ x : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)), Ψ (x⁻¹ * δ * (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
    (∀ (δ : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))), (∀ i, IsRegularSemisimple (normString K L (A i) σ (δ i))) →
      ∀ (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
        @Measure.IsHaarMeasure _ _ _ (borel _) τ' → @Measure.IsInvInvariant _ (borel _) _ τ' →
        ∀ Ψ : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
          ∃ W : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, Continuous W ∧ (∀ x, 0 ≤ W x) ∧ HasCompactSupport W ∧
            ∀ x : ((i : ι) → GL (Fin 2) (L ⊗[K] A i)), Ψ (x⁻¹ * δ * (MonoidHom.pi fun i : ι => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
    (∀ (γ : ((i : ι) → GL (Fin 2) (A i))), (∀ i, IsRegularSemisimple (γ i)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set ((i : ι) → GL (Fin 2) (A i)))) (borel _)),
        @Measure.IsHaarMeasure _ _ _ (borel _) τ →
        ∀ Ψ : ((i : ι) → GL (Fin 2) (A i)) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
          ∃ w : ((i : ι) → GL (Fin 2) (A i)) → ℝ, Continuous w ∧ (∀ x, 0 ≤ w x) ∧ HasCompactSupport w ∧
            ∀ x : ((i : ι) → GL (Fin 2) (A i)), Ψ (x⁻¹ * γ * x) ≠ 0 →
              @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : ((i : ι) → GL (Fin 2) (A i))) * x)) = 1) := by sorry
