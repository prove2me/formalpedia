-- Prove2me | Theorems.Thm_AutomorphicForm_semilocal_central_transfer_referenceMeasures_peel_step
-- name    : AutomorphicForm.semilocal_central_transfer_referenceMeasures_peel_step
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/c6480834-27e0-5f95-8aa3-902a1f6ce779
-- title:
--   Peel step for semi-local central transfer with reference measures
-- statement:
--   Throughout, $K \subseteq L$ is a finite extension of fields and $\sigma$ a $K$-algebra automorphism of $L$; $\iota$ is a finite index type; for each $i \in \iota$, $A i$ is a commutative topological $K$-algebra which is a Hausdorff, locally compact, second countable topological ring. For each $i$ there are finite-dimensional real normed spaces $X i$, $Y i$ and continuous 'coordinate readings' $\varepsilon_K i : \mathrm{GL}_2(A i) \to X i$ and $\varepsilon_L i : \mathrm{GL}_2(L \otimes_K A i) \to Y i$ (continuity is `hεK`, `hεL`), and a unit $c_i \in (A i)^\times$, whose associated central element is the scalar matrix $\mathrm{scalar}(c_i) \in \mathrm{GL}_2(A i)$.
--
--   The reference data are: measurable spaces $V i$; maps $\kappa i : \mathrm{GL}_2(A i) \to V i$ and $\kappa' i : \mathrm{GL}_2(L \otimes_K A i) \to V i$, each Borel measurable (`hκ`, `hκ'`) and injective (`hκi`, `hκ'i`); $\sigma$-finite measures $m i$ on $V i$ (`hm`) and, for each $\delta \in \mathrm{GL}_2(L \otimes_K A i)$, $\sigma$-finite measures $m' i\,\delta$ on $V i$ (`hm'`); complex weights $\mathrm{lam} : \iota \to \mathbb{C}$; Haar measures $\mu i$ on $\mathrm{GL}_2(A i)$ for the Borel $\sigma$-algebra which are in addition right invariant (`hμ`, `hμr`); and Haar measures $\mu' i$ on $\mathrm{GL}_2(L \otimes_K A i)$ (`hμ'`). Here $\mathrm{IsRegularSemisimple}\,g$ means that $\operatorname{tr}(g)^2 - 4\det(g)$ is a unit; `toTensorGL` is the map $\mathrm{GL}_2(A) \to \mathrm{GL}_2(L \otimes_K A)$ induced by $a \mapsto 1 \otimes a$; `sigmaGL` is the automorphism of $\mathrm{GL}_2(L \otimes_K A)$ induced by $\sigma \otimes \mathrm{id}$; $\mathrm{normString}(\delta) = \prod_{j=0}^{[L:K]-1} \mathrm{sigmaGL}^{j}(\delta)$; $\mathrm{IsNormConjugator}\,\gamma\,\delta\,y$ means $\mathrm{toTensorGL}(\gamma) = y^{-1}\,\mathrm{normString}(\delta)\,y$; the twisted centraliser of $\delta$ is $\{t : t\,\delta\,\mathrm{sigmaGL}(t)^{-1} = \delta\}$; and $\mathrm{Coupled}$ asserts that the image of $\tau'$ under $t \mapsto y^{-1} t y$ equals the image of $\tau$ under `toTensorGL`.
--
--   The hypotheses at one place are three groups. `hsecK`: for each $i$, each regular semisimple $\gamma \in \mathrm{GL}_2(A i)$, each Haar measure $\tau$ on the centraliser of $\gamma$, and each continuous compactly supported $f : \mathrm{GL}_2(A i) \to \mathbb{C}$, there is a continuous $w$ which is a section function for $(\gamma,\tau,f)$, i.e. $w \ge 0$, measurable, compactly supported, and $\int_\tau w(t x)\,d\tau = 1$ whenever $f(x^{-1}\gamma x) \neq 0$. `hsecL`: for each $i$ and $\delta$, each Haar and inversion-invariant measure $\tau'$ on the twisted centraliser of $\delta$ such that either $\mathrm{normString}(\delta)$ is regular semisimple, or there exist a Haar measure $\tau$ on the centraliser of $\mathrm{scalar}(c_i)$ and $s \in \mathbb{R}_{\ge 0}$, $s \neq 0$, with $(\kappa i)_*\tau = s \cdot m i$ and $(\kappa' i)_*\tau' = s \cdot m' i\,\delta$; then every continuous compactly supported $\varphi$ admits a continuous twisted section function $W$ (nonnegative, measurable, compactly supported, with $\int_{\tau'} W(t x)\,d\tau' = 1$ whenever $\varphi(x^{-1}\delta\,\mathrm{sigmaGL}(x)) \neq 0$). `heng`, the one-place transfer input: for each $i$, each $\varphi$ of the form $\Phi_1 \circ \varepsilon_L i$ with $\Phi_1$ smooth and $\varphi$ compactly supported, and each $f = F_1 \circ \varepsilon_K i$ with $F_1$ smooth and $f$ compactly supported, if there is a neighbourhood $V$ of $\mathrm{scalar}(c_i)$ such that for all $\delta$ with $\mathrm{normString}(\delta)$ regular semisimple, all regular semisimple $\gamma \in V$, all norm conjugators $y$, all Haar $\tau$, $\tau'$ on the respective centralisers which are coupled via $y$, every twisted orbital integral $I'$ of $\varphi$ against $\mu' i$, $\delta$, $\tau'$ equals every orbital integral $I$ of $f$ against $\mu i$, $\gamma$, $\tau$; then for all $\delta$, $y$ with $\mathrm{IsNormConjugator}\,\mathrm{scalar}(c_i)\,\delta\,y$, all Haar $\tau$ on the centraliser of $\mathrm{scalar}(c_i)$ and Haar, inversion-invariant $\tau'$ on the twisted centraliser of $\delta$ satisfying the reference relation ($\exists s \neq 0$ with $(\kappa i)_*\tau = s \cdot m i$ and $(\kappa' i)_*\tau' = s \cdot m' i\,\delta$), one has $I' = \mathrm{lam}\,i \cdot I$ for every twisted orbital integral $I'$ of $\varphi$ and orbital integral $I$ of $f$ at the central class.
--
--   The semi-local data are: Haar measures $\nu$ on $\prod_i \mathrm{GL}_2(A i)$ and $\nu'$ on $\prod_i \mathrm{GL}_2(L \otimes_K A i)$ for the Borel $\sigma$-algebras; a test function $F$ on $\prod_i \mathrm{GL}_2(A i)$ which factors as $F_1(\,i \mapsto \varepsilon_K i (g i)\,)$ with $F_1$ smooth on $\prod_i X i$ and which has compact support (`hF`); and $\Phi$ on $\prod_i \mathrm{GL}_2(L \otimes_K A i)$ factoring as $\Phi_1(\,i \mapsto \varepsilon_L i (g i)\,)$ with $\Phi_1$ smooth on $\prod_i Y i$, with compact support (`hΦ`). Write $\Theta$ for the product endomorphism $\mathrm{MonoidHom.pi}\,(i \mapsto \mathrm{sigmaGL}\circ \mathrm{eval}_i)$ of $\prod_i \mathrm{GL}_2(L \otimes_K A i)$, so that `sigmaCentralizer` $\Theta\,\delta = \{t : t\delta\Theta(t)^{-1} = \delta\}$.
--
--   `hreg` is the matching at componentwise regular data: for $\gamma$, $\delta$, $y$ in the product groups with every $\gamma i$ regular semisimple, every $\mathrm{normString}(\delta i)$ regular semisimple and every $y i$ a norm conjugator for $(\gamma i, \delta i)$, for all Haar $\tau$ on the centraliser of $\gamma$ in $\prod_i \mathrm{GL}_2(A i)$ and all Haar, inversion-invariant $\tau'$ on $\mathrm{sigmaCentralizer}\,\Theta\,\delta$ such that the image of $\tau'$ under $t \mapsto y^{-1} t y$ equals the image of $\tau$ under $s \mapsto (i \mapsto \mathrm{toTensorGL}((s)_i))$, and for all $I, I' \in \mathbb{C}$ such that $I'$ is given by $\int \Phi(x^{-1}\delta\Theta(x))\,W(x)\,d\nu'$ for some nonnegative measurable compactly supported $W$ with $\int_{\tau'} W(t x)\,d\tau' = 1$ whenever $\Phi(x^{-1}\delta\Theta(x)) \neq 0$, and $I$ is given by $\int F(x^{-1}\gamma x)\,w(x)\,d\nu$ for some nonnegative measurable compactly supported $w$ with $\int_\tau w(s x)\,d\tau = 1$ whenever $F(x^{-1}\gamma x) \neq 0$: then $I' = I$.
--
--   `ih` is the strong-induction hypothesis: the entire four-part conclusion below, with all of the above data re-quantified (index type $\iota_1$, algebras $A$, spaces $X$, $Y$, readings $\varepsilon_K$, $\varepsilon_L$, units $c$, reference data $V$, $\kappa$, $\kappa'$, $m$, $m'$, weights $\mathrm{lam}$, Haar measures $\mu$, $\mu'$, $\nu$, $\nu'$, the hypotheses `hsecK`, `hsecL`, `heng`, test functions $F$, $\Phi$ with their smoothness and support hypotheses, and `hreg`), is assumed for every finite index type $\iota_1$ with $\mathrm{card}\,\iota_1 < \mathrm{card}\,\iota$, with $K$, $L$, $\sigma$ fixed.
--
--   The conclusion is a conjunction of four assertions over $\iota$, where $\gamma_0 = (i \mapsto \mathrm{scalar}(c_i))$ and the 'product reference relation' for $(\tau,\tau',\delta)$ means: there is $s \in \mathbb{R}_{\ge 0}$, $s \neq 0$, with the image of $\tau$ under $t \mapsto (i \mapsto \kappa i\,((t)_i))$ equal to $s \cdot \mathrm{Measure.pi}\,m$ and the image of $\tau'$ under $t \mapsto (i \mapsto \kappa' i\,((t)_i))$ equal to $s \cdot \mathrm{Measure.pi}\,(i \mapsto m' i\,(\delta i))$, both for the product $\sigma$-algebra on $\prod_i V i$.
--
--   First conjunct: for all $\delta$, $y$ in $\prod_i \mathrm{GL}_2(L \otimes_K A i)$ with $\mathrm{IsNormConjugator}\,\mathrm{scalar}(c_i)\,(\delta i)\,(y i)$ for every $i$, for all Haar $\tau$ on the centraliser of $\gamma_0$ and all Haar, inversion-invariant $\tau'$ on $\mathrm{sigmaCentralizer}\,\Theta\,\delta$ satisfying the product reference relation, and for all $I, I' \in \mathbb{C}$ presented by the weighted integrals of the previous paragraph (with $\gamma$ replaced by $\gamma_0$): $I' = \bigl(\prod_i \mathrm{lam}\,i\bigr)\,I$.
--
--   Second conjunct: for the same $\delta$, $y$, $\tau$, $\tau'$ satisfying the same hypotheses and the same product reference relation, every continuous compactly supported $\Psi$ on $\prod_i \mathrm{GL}_2(L \otimes_K A i)$ admits a continuous, nonnegative, compactly supported $W$ with $\int_{\tau'} W(t x)\,d\tau' = 1$ for every $x$ with $\Psi(x^{-1}\delta\Theta(x)) \neq 0$.
--
--   Third conjunct: for every $\delta$ with $\mathrm{normString}(\delta i)$ regular semisimple for all $i$, every Haar, inversion-invariant $\tau'$ on $\mathrm{sigmaCentralizer}\,\Theta\,\delta$, and every continuous compactly supported $\Psi$, such a continuous nonnegative compactly supported twisted section $W$ exists.
--
--   Fourth conjunct: for every $\gamma$ in $\prod_i \mathrm{GL}_2(A i)$ with every $\gamma i$ regular semisimple, every Haar $\tau$ on the centraliser of $\gamma$, and every continuous compactly supported $\Psi$ on $\prod_i \mathrm{GL}_2(A i)$, there is a continuous, nonnegative, compactly supported $w$ with $\int_\tau w(s x)\,d\tau = 1$ for every $x$ with $\Psi(x^{-1}\gamma x) \neq 0$.
--
--   This is the inductive step in the proof of the semi-local central transfer identity in its reference-measure form: from the validity of the four assertions (central transfer with weight $\prod_i \mathrm{lam}\,i$, and the three section-function statements) for all strictly shorter products of places, their validity over the full index set $\iota$ follows. It is used by [`AutomorphicForm.semilocal_central_transfer_of_forall_oneplace_of_referenceMeasures`](thm.html#AutomorphicForm.semilocal_central_transfer_of_forall_oneplace_of_referenceMeasures), which runs the induction on $\mathrm{card}\,\iota$ and thereby passes from the one-place transfer hypotheses at central classes to the semi-local statement needed for comparing twisted and ordinary orbital integrals in base change for $\mathrm{GL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_semilocal_central_transfer_referenceMeasures_peel_step.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions NNReal

theorem AutomorphicForm.semilocal_central_transfer_referenceMeasures_peel_step
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
          I' = I)

    (ih : ∀ {ι₁ : Type} [Fintype ι₁] [DecidableEq ι₁]
      (A : ι₁ → Type) [∀ i, CommRing (A i)] [∀ i, Algebra K (A i)] [∀ i, TopologicalSpace (A i)]
      [∀ i, IsTopologicalRing (A i)] [∀ i, T2Space (A i)] [∀ i, LocallyCompactSpace (A i)]
      [∀ i, SecondCountableTopology (A i)]
      (X Y : ι₁ → Type) [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℝ (X i)] [∀ i, FiniteDimensional ℝ (X i)]
      [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace ℝ (Y i)] [∀ i, FiniteDimensional ℝ (Y i)]
      (εK : ∀ i, GL (Fin 2) (A i) → X i) (hεK : ∀ i, Continuous (εK i))
      (εL : ∀ i, GL (Fin 2) (L ⊗[K] A i) → Y i) (hεL : ∀ i, Continuous (εL i))
      (c : ∀ i, (A i)ˣ)

      (V : ι₁ → Type) [∀ i, MeasurableSpace (V i)]
      (κ : ∀ i, GL (Fin 2) (A i) → V i) (hκ : ∀ i, Measurable[glBorelOf (A i)] (κ i)) (hκi : ∀ i, Function.Injective (κ i))
      (κ' : ∀ i, GL (Fin 2) (L ⊗[K] A i) → V i) (hκ' : ∀ i, Measurable[glBorelOf (L ⊗[K] A i)] (κ' i))
      (hκ'i : ∀ i, Function.Injective (κ' i))
      (m : ∀ i, Measure (V i)) (hm : ∀ i, SigmaFinite (m i))
      (m' : ∀ i, GL (Fin 2) (L ⊗[K] A i) → Measure (V i)) (hm' : ∀ i δ, SigmaFinite (m' i δ))
      (lam : ι₁ → ℂ)
      (μ : ∀ i, @Measure (GL (Fin 2) (A i)) (glBorelOf (A i)))
      (hμ : ∀ i, @Measure.IsHaarMeasure _ _ _ (glBorelOf (A i)) (μ i))
      (hμr : ∀ i, @Measure.IsMulRightInvariant _ (glBorelOf (A i)) _ (μ i))
      (μ' : ∀ i, @Measure (GL (Fin 2) (L ⊗[K] A i)) (glBorelOf (L ⊗[K] A i)))
      (hμ' : ∀ i, @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] A i)) (μ' i))
      (hsecK : ∀ (i : ι₁) (γ : GL (Fin 2) (A i)), IsRegularSemisimple γ →
      ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (A i)))) (centralizerBorel (A i) γ),
      @Measure.IsHaarMeasure _ _ _ (centralizerBorel (A i) γ) τ →
      ∀ f : GL (Fin 2) (A i) → ℂ, Continuous f → HasCompactSupport f →
      ∃ w : GL (Fin 2) (A i) → ℝ, IsSectionFnOn (A i) γ τ f w ∧ Continuous w)
      (hsecL : ∀ (i : ι₁) (δ : GL (Fin 2) (L ⊗[K] A i)),
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
      (heng : ∀ (i : ι₁) (φ : GL (Fin 2) (L ⊗[K] A i) → ℂ),
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
      (ν : @Measure ((i : ι₁) → GL (Fin 2) (A i)) (borel _)) (hν : @Measure.IsHaarMeasure ((i : ι₁) → GL (Fin 2) (A i)) _ _ (borel _) ν)
      (ν' : @Measure ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i)) (borel _)) (hν' : @Measure.IsHaarMeasure ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i)) _ _ (borel _) ν')
      (F : ((i : ι₁) → GL (Fin 2) (A i)) → ℂ)
      (hF : (∃ F₁ : ((i : ι₁) → X i) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F₁ ∧ ∀ g, F g = F₁ (fun i => εK i (g i))) ∧
      HasCompactSupport F)
      (Φ : ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i)) → ℂ)
      (hΦ : (∃ Φ₁ : ((i : ι₁) → Y i) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ₁ ∧ ∀ g, Φ g = Φ₁ (fun i => εL i (g i))) ∧
      HasCompactSupport Φ)
      (hreg : ∀ (γ : ((i : ι₁) → GL (Fin 2) (A i))) (δ y : ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i))),
      (∀ i, IsRegularSemisimple (γ i)) → (∀ i, IsRegularSemisimple (normString K L (A i) σ (δ i))) →
      (∀ i, IsNormConjugator K L (A i) σ (γ i) (δ i) (y i)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set ((i : ι₁) → GL (Fin 2) (A i)))) (borel _))
      (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : ι₁ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι₁ => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ → @Measure.IsHaarMeasure _ _ _ (borel _) τ' →
      @Measure.IsInvInvariant _ (borel _) _ τ' →
      @Measure.map _ _ (borel _) (borel ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i)))
      (fun t : sigmaCentralizer (MonoidHom.pi fun i : ι₁ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι₁ => GL (Fin 2) (L ⊗[K] A i)) i)) δ => y⁻¹ * (t : ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i))) * y) τ' =
      @Measure.map _ _ (borel _) (borel ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i)))
      (fun s : Subgroup.centralizer ({γ} : Set ((i : ι₁) → GL (Fin 2) (A i))) => fun i => toTensorGL K L (A i) ((s : ((i : ι₁) → GL (Fin 2) (A i))) i)) τ →
      ∀ I I' : ℂ,
      (∃ W : ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, (∀ x, 0 ≤ W x) ∧ Measurable[borel ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i))] W ∧ HasCompactSupport W ∧
      (∀ x : ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i)), Φ (x⁻¹ * δ * (MonoidHom.pi fun i : ι₁ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι₁ => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
      I' = @integral _ ℂ _ _ (borel ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i))) ν' (fun x => Φ (x⁻¹ * δ * (MonoidHom.pi fun i : ι₁ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι₁ => GL (Fin 2) (L ⊗[K] A i)) i)) x) * (W x : ℂ))) →
      (∃ w : ((i : ι₁) → GL (Fin 2) (A i)) → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable[borel ((i : ι₁) → GL (Fin 2) (A i))] w ∧ HasCompactSupport w ∧
      (∀ x : ((i : ι₁) → GL (Fin 2) (A i)), F (x⁻¹ * γ * x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : ((i : ι₁) → GL (Fin 2) (A i))) * x)) = 1) ∧
      I = @integral _ ℂ _ _ (borel ((i : ι₁) → GL (Fin 2) (A i))) ν (fun x => F (x⁻¹ * γ * x) * (w x : ℂ))) →
      I' = I),
      Fintype.card ι₁ < Fintype.card ι →
      (∀ (δ y : ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i))),
      (∀ i, IsNormConjugator K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) (δ i) (y i)) →
      ∀ (τ : @Measure (Subgroup.centralizer
      ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : ι₁) → GL (Fin 2) (A i)))} : Set ((i : ι₁) → GL (Fin 2) (A i)))) (borel _))
      (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : ι₁ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι₁ => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ → @Measure.IsHaarMeasure _ _ _ (borel _) τ' →
      @Measure.IsInvInvariant _ (borel _) _ τ' →
      (∃ s : ℝ≥0, s ≠ 0 ∧
      @Measure.map _ _ (borel _) MeasurableSpace.pi
      (fun t : Subgroup.centralizer ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : ι₁) → GL (Fin 2) (A i)))} : Set ((i : ι₁) → GL (Fin 2) (A i))) =>
      fun i => κ i ((t : ((i : ι₁) → GL (Fin 2) (A i))) i)) τ =
      s • Measure.pi m ∧
      @Measure.map _ _ (borel _) MeasurableSpace.pi
      (fun t : sigmaCentralizer (MonoidHom.pi fun i : ι₁ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι₁ => GL (Fin 2) (L ⊗[K] A i)) i)) δ => fun i => κ' i ((t : ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i))) i)) τ' =
      s • Measure.pi (fun i => m' i (δ i))) →
      ∀ I I' : ℂ,
      (∃ W : ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, (∀ x, 0 ≤ W x) ∧ Measurable[borel ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i))] W ∧ HasCompactSupport W ∧
      (∀ x : ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i)), Φ (x⁻¹ * δ * (MonoidHom.pi fun i : ι₁ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι₁ => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
      I' = @integral _ ℂ _ _ (borel ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i))) ν' (fun x => Φ (x⁻¹ * δ * (MonoidHom.pi fun i : ι₁ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι₁ => GL (Fin 2) (L ⊗[K] A i)) i)) x) * (W x : ℂ))) →
      (∃ w : ((i : ι₁) → GL (Fin 2) (A i)) → ℝ, (∀ x, 0 ≤ w x) ∧ Measurable[borel ((i : ι₁) → GL (Fin 2) (A i))] w ∧ HasCompactSupport w ∧
      (∀ x : ((i : ι₁) → GL (Fin 2) (A i)), F (x⁻¹ * (fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) * x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : ((i : ι₁) → GL (Fin 2) (A i))) * x)) = 1) ∧
      I = @integral _ ℂ _ _ (borel ((i : ι₁) → GL (Fin 2) (A i))) ν
      (fun x => F (x⁻¹ * (fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) * x) * (w x : ℂ))) →
      I' = (∏ i, lam i) * I) ∧
      (∀ (δ y : ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i))),
      (∀ i, IsNormConjugator K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) (δ i) (y i)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : ι₁) → GL (Fin 2) (A i)))} : Set ((i : ι₁) → GL (Fin 2) (A i)))) (borel _))
      (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : ι₁ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι₁ => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ → @Measure.IsHaarMeasure _ _ _ (borel _) τ' →
      @Measure.IsInvInvariant _ (borel _) _ τ' →
      (∃ s : ℝ≥0, s ≠ 0 ∧
      @Measure.map _ _ (borel _) MeasurableSpace.pi
      (fun t : Subgroup.centralizer ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : ι₁) → GL (Fin 2) (A i)))} : Set ((i : ι₁) → GL (Fin 2) (A i))) =>
      fun i => κ i ((t : ((i : ι₁) → GL (Fin 2) (A i))) i)) τ =
      s • Measure.pi m ∧
      @Measure.map _ _ (borel _) MeasurableSpace.pi
      (fun t : sigmaCentralizer (MonoidHom.pi fun i : ι₁ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι₁ => GL (Fin 2) (L ⊗[K] A i)) i)) δ => fun i => κ' i ((t : ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i))) i)) τ' =
      s • Measure.pi (fun i => m' i (δ i))) →
      ∀ Ψ : ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i)) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
      ∃ W : ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, Continuous W ∧ (∀ x, 0 ≤ W x) ∧ HasCompactSupport W ∧
      ∀ x : ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i)), Ψ (x⁻¹ * δ * (MonoidHom.pi fun i : ι₁ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι₁ => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
      (∀ (δ : ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i))), (∀ i, IsRegularSemisimple (normString K L (A i) σ (δ i))) →
      ∀ (τ' : @Measure (sigmaCentralizer (MonoidHom.pi fun i : ι₁ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι₁ => GL (Fin 2) (L ⊗[K] A i)) i)) δ) (borel _)),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ' → @Measure.IsInvInvariant _ (borel _) _ τ' →
      ∀ Ψ : ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i)) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
      ∃ W : ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i)) → ℝ, Continuous W ∧ (∀ x, 0 ≤ W x) ∧ HasCompactSupport W ∧
      ∀ x : ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i)), Ψ (x⁻¹ * δ * (MonoidHom.pi fun i : ι₁ => (sigmaGL K L (A i) σ).comp (Pi.evalMonoidHom (fun i : ι₁ => GL (Fin 2) (L ⊗[K] A i)) i)) x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ' (fun t => W ((t : ((i : ι₁) → GL (Fin 2) (L ⊗[K] A i))) * x)) = 1) ∧
      (∀ (γ : ((i : ι₁) → GL (Fin 2) (A i))), (∀ i, IsRegularSemisimple (γ i)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set ((i : ι₁) → GL (Fin 2) (A i)))) (borel _)),
      @Measure.IsHaarMeasure _ _ _ (borel _) τ →
      ∀ Ψ : ((i : ι₁) → GL (Fin 2) (A i)) → ℂ, Continuous Ψ → HasCompactSupport Ψ →
      ∃ w : ((i : ι₁) → GL (Fin 2) (A i)) → ℝ, Continuous w ∧ (∀ x, 0 ≤ w x) ∧ HasCompactSupport w ∧
      ∀ x : ((i : ι₁) → GL (Fin 2) (A i)), Ψ (x⁻¹ * γ * x) ≠ 0 →
      @integral _ ℝ _ _ (borel _) τ (fun s => w ((s : ((i : ι₁) → GL (Fin 2) (A i))) * x)) = 1)) :
    (∀ (δ y : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))),
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
          I' = (∏ i, lam i) * I) ∧
    (∀ (δ y : ((i : ι) → GL (Fin 2) (L ⊗[K] A i))),
      (∀ i, IsNormConjugator K L (A i) σ (Matrix.GeneralLinearGroup.scalar (Fin 2) (c i)) (δ i) (y i)) →
      ∀ (τ : @Measure (Subgroup.centralizer ({(fun i => Matrix.GeneralLinearGroup.scalar (Fin 2) (c i) : ((i : ι) → GL (Fin 2) (A i)))} : Set ((i : ι) → GL (Fin 2) (A i)))) (borel _))
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
