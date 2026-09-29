-- Prove2me | Theorems.Thm_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom
-- name    : AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/0c101cba-a922-5c26-9f9d-3245458c71f5
-- title:
--   Archimedean central base change comparison with Kottwitz sign
-- statement:
--   Throughout, $K$ and $L$ are number fields with $L$ a $K$-algebra, `h2` asserts $[L:K]=2$, and $\sigma$ is a $K$-algebra automorphism of $L$ which, by `hgen`, generates the group of $K$-automorphisms of $L$ in the sense that every $\tau \colon L \simeq_K L$ lies in the subgroup of integer powers of $\sigma$. Furthermore `hprime` asserts that $[L:K]$ is a prime natural number.
--
--   On the group side, $\gamma \in GL_2(\mathbb{A}_{K,\infty})$ (the infinite adele ring of $K$) is assumed by `hγ` to be a scalar matrix $c \cdot 1$ for some unit $c$ of $\mathbb{A}_{K,\infty}$, and $\delta, y \in GL_2(L \otimes_K \mathbb{A}_{K,\infty})$ satisfy `hδ`, the predicate `IsNormConjugator`: the entrywise image of $\gamma$ under $a \mapsto 1 \otimes a$ equals $y^{-1}\,\delta\,\sigma(\delta)\cdots\sigma^{[L:K]-1}(\delta)\,y$, where $\sigma$ acts on $GL_2(L\otimes_K\mathbb{A}_{K,\infty})$ entrywise through $\sigma \otimes \mathrm{id}$ (the norm string `normString` being the ordered product of the iterates of $\delta$).
--
--   Two Haar measures are fixed: $\tau$, a Haar measure for the Borel structure on the centraliser of $\{\gamma\}$ in $GL_2(\mathbb{A}_{K,\infty})$ (`hτ`), and $\tau'$, a Haar measure for the Borel structure on the $\sigma$-twisted centraliser $\{t : t\,\delta\,\sigma(t)^{-1} = \delta\}$ of $\delta$ in $GL_2(L \otimes_K \mathbb{A}_{K,\infty})$ (`hτ'`).
--
--   The hypothesis `hnorm` normalises this pair of measures by a common Gram constant. With $\mathbb{A}_{K,\infty}$ made an $\mathbb{R}$-algebra through its identification with the mixed space of $K$, with $L \otimes_K \mathbb{A}_{K,\infty}$ an $\mathbb{R}$-algebra through $a \mapsto 1 \otimes a$, and with $M_2(L\otimes_K\mathbb{A}_{K,\infty})$ carrying its Borel structure, `hnorm` asserts the existence of natural numbers $n_1, n_2$, families $e_1 \colon \mathrm{Fin}\,n_1 \to M_2(L\otimes_K\mathbb{A}_{K,\infty})$ and $e_2 \colon \mathrm{Fin}\,n_2 \to M_2(L\otimes_K\mathbb{A}_{K,\infty})$, and an extended nonnegative real $s$ with $s \neq 0$ and $s \neq \infty$, such that: $e_1$ is $\mathbb{R}$-linearly independent with $\mathbb{R}$-span the entrywise image of $M_2(\mathbb{A}_{K,\infty})$ under $a \mapsto 1 \otimes a$; $e_2$ is $\mathbb{R}$-linearly independent with $\mathbb{R}$-span the twisted commutant $\{X : X\delta = \delta\,\sigma(X)\}$; the pushforward of $\tau$ along the entrywise embedding of the centraliser into $M_2(L\otimes_K\mathbb{A}_{K,\infty})$ equals $s$ times the measure obtained from $\sqrt{|\det(\mathrm{Tr}_{\mathbb{R}}(\mathrm{tr}(e_1(i)\,e_1(j))))_{ij}|}$ times the pushforward of Lebesgue measure on $\mathbb{R}^{n_1}$ along $c \mapsto \sum_i c_i\,e_1(i)$, weighted by the density $X \mapsto |N_{\mathbb{R}}(\det X)|^{-1}$; and the pushforward of $\tau'$ along the inclusion of the twisted centraliser into $M_2(L\otimes_K\mathbb{A}_{K,\infty})$ equals $s$ times the corresponding measure built from $e_2$ and $n_2$, with the same $s$.
--
--   Four local comparison hypotheses and one bridge hypothesis are assumed, each as a closed statement; their inner hypothesis lists (Haar measures, smooth compactly supported test functions, local matching conditions) are summarised here.
--
--   `hram` (real place of $K$ under a complex place of $L$, positive scalar): for all Haar measures $\mu_A$ on $GL_2(\mathbb{R})$ and $\mu_L$ on $GL_2(\mathbb{C}\otimes_\mathbb{R}\mathbb{R})$, all $\varphi \colon GL_2(\mathbb{C}) \to \mathbb{C}$ and $f \colon GL_2(\mathbb{R}) \to \mathbb{C}$ which have compact support and arise from smooth functions of the matrix entries, every unit $c$ of $\mathbb{R}$ with $c > 0$, and under the matching hypothesis `hmatch` — there is a neighbourhood $V$ of $c\cdot 1$ such that for every $\delta$ whose norm string is regular semisimple (that is, $\mathrm{tr}^2 - 4\det$ of it is a unit), every regular semisimple $\gamma \in V$, every norm conjugator $y$, every pair of Haar measures $\tau,\tau'$ on the centraliser and twisted centraliser which are coupled (the pushforward of $\tau'$ along $t \mapsto y^{-1}ty$ equals the pushforward of $\tau$ along the entrywise embedding), and all $I, I'$, a $\sigma$-twisted orbital integral value $I'$ of $\varphi$ transported through $\mathbb{C}\otimes_\mathbb{R}\mathbb{R} \cong \mathbb{C}$ and an orbital integral value $I$ of $f$ satisfy $I' = I$ — then for all $\delta, y$ with $c\cdot 1$ norm-conjugate to $\delta$ via $y$, all Haar $\tau, \tau'$ on the relevant centraliser and twisted centraliser which are coupled, and all $I'$: if $I'$ is a twisted orbital integral of the transported $\varphi$ at $\delta$ with respect to $\mu_L$ and $\tau'$, then $I'$ is also an orbital integral of $f$ at $c \cdot 1$ with respect to $\mu_A$ and $\tau$ (sign $+1$).
--
--   `hramNeg` is the same situation with $c < 0$, where the matching hypothesis carries in addition the clause that the orbital integral of $f$ vanishes at every regular semisimple $\gamma \in V$ admitting no norm, and where the conclusion is taken under the common-$s$ Gram normalisation of $\tau$ and $\tau'$ over $\mathbb{C}\otimes_\mathbb{R}\mathbb{R}$ (the same shape as `hnorm`, with $e_1$ spanning the image of $M_2(\mathbb{R})$ under $x \mapsto 1 \otimes x$ and $e_2$ spanning the commutant twisted by complex conjugation) rather than under coupledness: it concludes that $-I'$ is an orbital integral of $f$ at $c\cdot 1$ (sign $-1$).
--
--   `hsplitR` and `hsplitC` treat the split places. For $\sigma \neq 1$, an algebra structure making $K$ a subfield of $\mathbb{R}$ (respectively $\mathbb{C}$) and a $K$-algebra homomorphism $\iota \colon L \to \mathbb{R}$ (respectively $L \to \mathbb{C}$), Haar measures on $GL_2(\mathbb{R})$ and $GL_2(L\otimes_K\mathbb{R})$ (respectively over $\mathbb{C}$), a test function $\varphi$ on $GL_2(L\otimes_K\mathbb{R})$ of compact support which is a smooth function of the entries of the $[L:K]$ components produced by the splitting isomorphism `SplitPlace.psiGL` attached to $\sigma$, $\iota$, `hprime` and $\sigma \neq 1$, a test function $f$ of the same kind on $GL_2(\mathbb{R})$ (respectively $GL_2(\mathbb{C})$), a unit $c$, and the corresponding local matching hypothesis near $c\cdot 1$: for all $\delta, y$ with $c \cdot 1$ norm-conjugate to $\delta$ via $y$, all coupled Haar measures $\tau, \tau'$, and every $I'$, a twisted orbital integral value $I'$ of $\varphi$ at $\delta$ is also an orbital integral value of $f$ at $c\cdot 1$.
--
--   `hgc` is the bridge from the Gram normalisation to coupledness at a real place under a complex place with positive scalar component: for every unit $c$ of $\mathbb{R}$ with $c>0$, every $\delta, y$ in $GL_2(\mathbb{C}\otimes_\mathbb{R}\mathbb{R})$ with $c\cdot1$ norm-conjugate to $\delta$ via $y$ relative to complex conjugation, and all Haar measures $\tau, \tau'$ on the centraliser of $c\cdot 1$ and the twisted centraliser of $\delta$ satisfying the common-$s$ Gram normalisation described above, there exists $y'$ which is again a norm conjugator for $c\cdot 1$ and $\delta$ and for which $\tau$ and $\tau'$ are coupled through $y'$.
--
--   Under all of these hypotheses the conclusion is: for every $\varphi_a \colon GL_2(\mathbb{A}_{L,\infty}) \to \mathbb{C}$ which is an archimedean test factor for $L$ (compactly supported and equal to a smooth function of its matrix entries read in the mixed space of $L$), every $f_a \colon GL_2(\mathbb{A}_{K,\infty}) \to \mathbb{C}$ which is an archimedean test factor for $K$, such that $\varphi_a$ and $f_a$ match in the archimedean sense — that is, the composite of $\varphi_a$ with the entrywise map induced by the ring homomorphism $L\otimes_K\mathbb{A}_{K,\infty} \to \mathbb{A}_{L,\infty}$ and $f_a$ satisfy, with respect to the canonical Haar measures `archHaarL` and `archHaarK`, both the equality of twisted orbital integrals with orbital integrals at all regular semisimple norm strings with coupled Haar measures and the vanishing of orbital integrals of $f_a$ at regular semisimple elements admitting no norm — and for all $I, I' \in \mathbb{C}$ such that $I'$ is a twisted orbital integral of $\varphi_a$ composed with that entrywise map at $\delta$ with respect to `archHaarL` and $\tau'$, and $I$ is an orbital integral of $f_a$ at $\gamma$ with respect to `archHaarK` and $\tau$, one has
--   $$I' = (-1)^{r}\, I,$$
--   where $r$ is the number of infinite places $w$ of $K$ such that for no unit $z$ of $L \otimes_K K_w$ is the component of $\delta$ at $w$ — its image under the map induced entrywise by $\mathrm{id}_L \otimes (\text{evaluation at } w)$ — $\sigma$-conjugate to the scalar matrix $z\cdot 1$, $\sigma$-conjugacy of $\delta_1$ and $\delta_2$ meaning $\delta_2 = x^{-1}\delta_1\,\sigma(x)$ for some $x$.
--
--   This is the archimedean assembly step of the base-change comparison of twisted orbital integrals with orbital integrals at a central element of $GL_2(\mathbb{A}_{K,\infty})$ for a quadratic extension $L/K$, carrying the sign $(-1)^r$ of Kottwitz type, with $r$ the number of infinite places at which the local component of $\delta$ is not $\sigma$-conjugate to a scalar; the four local comparisons (ramified real place with positive and with negative scalar component, split real and split complex places) and the passage from the common Gram normalisation of the measures to coupledness are taken as hypotheses. It is used by [`AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_finrank_eq_two`](thm.html#AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_finrank_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_SplitFibreIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open AutomorphicForm
open scoped TensorProduct
open scoped TensorProduct.RightActions

theorem AutomorphicForm.twistedOrbitalIntegral_eq_neg_one_pow_mul_orbitalIntegral_scalar_arch_of_forall_conjAe_of_forall_gram_of_forall_algHom
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (γ : GL (Fin 2) (InfiniteAdeleRing K))
    (hγ : ∃ c : (InfiniteAdeleRing K)ˣ, γ = Matrix.GeneralLinearGroup.scalar (Fin 2) c)
    (δ y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
    (hδ : AutomorphicForm.IsNormConjugator K L (InfiniteAdeleRing K) σ γ δ y)
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
      (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) γ))
    (hτ : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) γ) τ)
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
      (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) τ')
    (hnorm :
      letI : Algebra ℝ (InfiniteAdeleRing K) :=
        ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
          (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
      letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
        ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
          (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
      letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) := borel _
      letI := AutomorphicForm.centralizerBorel (InfiniteAdeleRing K) γ
      letI := AutomorphicForm.twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ
      ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
        (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) (s : ENNReal),
        s ≠ 0 ∧ s ≠ ⊤ ∧
        LinearIndependent ℝ e₁ ∧
          (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
            Set.range (fun Y : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K) =>
              Y.map (Algebra.TensorProduct.includeRight :
                InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K)) ∧
        LinearIndependent ℝ e₂ ∧
          (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) =
            {X | X * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) =
              (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) *
                X.map (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ)} ∧
        Measure.map (fun t : ↥(Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K)))) =>
            ((t : GL (Fin 2) (InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)).map
              (Algebra.TensorProduct.includeRight :
                InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K)) τ =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                Measure.map (fun c : Fin n₁ → ℝ => ∑ i, c i • e₁ i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
        Measure.map (fun t : ↥(AutomorphicForm.twistedCentralizer K L (InfiniteAdeleRing K) σ δ) =>
            ((t : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) τ' =
          s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                  Algebra.trace ℝ (L ⊗[K] InfiniteAdeleRing K) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                Measure.map (fun c : Fin n₂ → ℝ => ∑ i, c i • e₂ i) volume).withDensity
              (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K) =>
                (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))
    (hprime : (Module.finrank K L).Prime)
    (hram : ∀
      (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
      (μL : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
      (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
      (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μL)
      (φ : GL (Fin 2) ℂ → ℂ)
      (hφ : (∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
        ∀ g, φ g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φ)
      (f : GL (Fin 2) ℝ → ℂ)
      (hf : (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
        ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f)
      (c : ℝˣ) (hc : 0 < (c : ℝ))
      (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
        ∀ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsRegularSemisimple (normString ℝ ℂ ℝ Complex.conjAe δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsNormConjugator ℝ ℂ ℝ Complex.conjAe γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ))
          (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
          Coupled ℝ ℂ ℝ Complex.conjAe γ δ y τ τ' →
          ∀ I I' : ℂ,
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
              (fun z => φ (Matrix.GeneralLinearGroup.map
                (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                  (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
            IsOrbitalIntegralOn ℝ μA γ τ f I → I' = I),
      ∀ δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y →
        ∀ (τ : @Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
              (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
          (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
          Coupled ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ' →
          ∀ I' : ℂ,
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
              (fun z => φ (Matrix.GeneralLinearGroup.map
                (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                  (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
            IsOrbitalIntegralOn ℝ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I')
    (hramNeg : ∀ (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
      (μL : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
      (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
      (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μL)
      (φ : GL (Fin 2) ℂ → ℂ)
      (hφ : (∃ Φ : (Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
        ∀ g, φ g = Φ (fun i j => (g : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧ HasCompactSupport φ)
      (f : GL (Fin 2) ℝ → ℂ)
      (hf : (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
        ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f)
      (c : ℝˣ) (hc : (c : ℝ) < 0)
      (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
        (∀ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsRegularSemisimple (normString ℝ ℂ ℝ Complex.conjAe δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsNormConjugator ℝ ℂ ℝ Complex.conjAe γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ))
          (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
          Coupled ℝ ℂ ℝ Complex.conjAe γ δ y τ τ' →
          ∀ I I' : ℂ,
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
              (fun z => φ (Matrix.GeneralLinearGroup.map
                (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                  (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
            IsOrbitalIntegralOn ℝ μA γ τ f I → I' = I) ∧
        (∀ γ ∈ V, IsRegularSemisimple γ →
          (¬ ∃ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsNormOf ℝ ℂ ℝ Complex.conjAe γ δ) →
          ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ)),
            @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
            ∀ I : ℂ, IsOrbitalIntegralOn ℝ μA γ τ f I → I = 0)),
      ∀ δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y →
        ∀ (τ : @Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
              (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
          (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
            (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
          (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borel _
           letI := centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
           letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
           ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))
             (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) (s : ENNReal),
             s ≠ 0 ∧ s ≠ ⊤ ∧
             LinearIndependent ℝ e₁ ∧
               (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
                 Set.range (fun Y : Matrix (Fin 2) (Fin 2) ℝ =>
                   Y.map (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) ∧
             LinearIndependent ℝ e₂ ∧
               (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
                 {X | X * (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) =
                   (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) * X.map (sigmaTensor ℝ ℂ ℝ Complex.conjAe)} ∧
             Measure.map (fun t : ↥(Subgroup.centralizer
                   ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) =>
                 ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map
                   (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) τ =
               s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                       Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                     Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
                   (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                     (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
             Measure.map (fun t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) =>
                 ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) τ' =
               s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                       Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                     Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
                   (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                     (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹)) →
          ∀ I' : ℂ,
            IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
              (fun z => φ (Matrix.GeneralLinearGroup.map
                (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                  (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom z : GL (Fin 2) ℂ)) I' →
            IsOrbitalIntegralOn ℝ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f (-I'))
    (hsplitR : ∀
      (hσ : σ ≠ 1) [Algebra K ℝ] (ι : L →ₐ[K] ℝ)
      (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
      (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
      (μL : @Measure (GL (Fin 2) (L ⊗[K] ℝ)) (glBorelOf (L ⊗[K] ℝ)))
      (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] ℝ)) μL)
      (φ : GL (Fin 2) (L ⊗[K] ℝ) → ℂ)
      (hφ : (∃ Φ : (Fin (Module.finrank K L) → Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
        ∀ g, φ g = Φ (fun k i j =>
          ((SplitPlace.psiGL ℝ σ ι hprime hσ g k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧
        HasCompactSupport φ)
      (f : GL (Fin 2) ℝ → ℂ)
      (hf : (∃ F : (Fin 2 → Fin 2 → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) F ∧
        ∀ g, f g = F (fun i j => (g : Matrix (Fin 2) (Fin 2) ℝ) i j)) ∧ HasCompactSupport f)
      (c : ℝˣ)
      (hmatch : ∃ V ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
        ∀ δ : GL (Fin 2) (L ⊗[K] ℝ), IsRegularSemisimple (normString K L ℝ σ δ) →
        ∀ γ ∈ V, IsRegularSemisimple γ →
        ∀ y : GL (Fin 2) (L ⊗[K] ℝ), IsNormConjugator K L ℝ σ γ δ y →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ))
          (τ' : @Measure (twistedCentralizer K L ℝ σ δ) (twistedCentralizerBorel K L ℝ σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℝ σ δ) τ' →
          Coupled K L ℝ σ γ δ y τ τ' →
          ∀ I I' : ℂ, IsTwistedOrbitalIntegralOn K L ℝ σ μL δ τ' φ I' →
            IsOrbitalIntegralOn ℝ μA γ τ f I → I' = I),
      ∀ δ y : GL (Fin 2) (L ⊗[K] ℝ),
        IsNormConjugator K L ℝ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y →
        ∀ (τ : @Measure (Subgroup.centralizer
              ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
              (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
          (τ' : @Measure (twistedCentralizer K L ℝ σ δ) (twistedCentralizerBorel K L ℝ σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L ℝ σ δ) τ' →
          Coupled K L ℝ σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y τ τ' →
          ∀ I' : ℂ, IsTwistedOrbitalIntegralOn K L ℝ σ μL δ τ' φ I' →
            IsOrbitalIntegralOn ℝ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I')
    (hsplitC : ∀
      (hσ : σ ≠ 1) [Algebra K ℂ] (ι : L →ₐ[K] ℂ)
      (μA : @Measure (GL (Fin 2) ℂ) (glBorelOf ℂ))
      (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℂ) μA)
      (μL : @Measure (GL (Fin 2) (L ⊗[K] ℂ)) (glBorelOf (L ⊗[K] ℂ)))
      (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] ℂ)) μL)
      (φ : GL (Fin 2) (L ⊗[K] ℂ) → ℂ)
      (hφ : (∃ Φ : (Fin (Module.finrank K L) → Fin 2 → Fin 2 → ℂ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
        ∀ g, φ g = Φ (fun k i j =>
          ((SplitPlace.psiGL ℂ σ ι hprime hσ g k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) i j)) ∧
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
            IsOrbitalIntegralOn ℂ μA γ τ f I → I' = I),
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
            IsOrbitalIntegralOn ℂ μA (Matrix.GeneralLinearGroup.scalar (Fin 2) c) τ f I')
    (hgc : ∀ (c : ℝˣ) (hc : 0 < (c : ℝ))
      (δ y : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
      (hδ : IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y)
      (τ : @Measure (Subgroup.centralizer
          ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ)))
          (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)))
      (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
        (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
      (hτ : @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)) τ)
      (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ')
      (hgram : (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) := borel _
         letI := centralizerBorel ℝ (Matrix.GeneralLinearGroup.scalar (Fin 2) c)
         letI := twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ
         ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))
           (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) (s : ENNReal),
           s ≠ 0 ∧ s ≠ ⊤ ∧
           LinearIndependent ℝ e₁ ∧
             (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
               Set.range (fun Y : Matrix (Fin 2) (Fin 2) ℝ =>
                 Y.map (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) ∧
           LinearIndependent ℝ e₂ ∧
             (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) =
               {X | X * (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) =
                 (δ : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ)) * X.map (sigmaTensor ℝ ℂ ℝ Complex.conjAe)} ∧
           Measure.map (fun t : ↥(Subgroup.centralizer
                 ({Matrix.GeneralLinearGroup.scalar (Fin 2) c} : Set (GL (Fin 2) ℝ))) =>
               ((t : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).map
                 (fun x : ℝ => ((1 : ℂ) ⊗ₜ[ℝ] x : ℂ ⊗[ℝ] ℝ))) τ =
             s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                     Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                   Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
                 (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                   (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
           Measure.map (fun t : ↥(twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) =>
               ((t : GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ))) τ' =
             s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                     Algebra.trace ℝ (ℂ ⊗[ℝ] ℝ) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                   Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
                 (fun X : Matrix (Fin 2) (Fin 2) (ℂ ⊗[ℝ] ℝ) =>
                   (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))),
      ∃ y' : GL (Fin 2) (ℂ ⊗[ℝ] ℝ),
        IsNormConjugator ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y' ∧
        Coupled ℝ ℂ ℝ Complex.conjAe (Matrix.GeneralLinearGroup.scalar (Fin 2) c) δ y' τ τ') :
    ∀ (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ), AutomorphicForm.IsArchTestFactor L φa →
      ∀ (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ), AutomorphicForm.IsArchTestFactor K fa →
        AutomorphicForm.AreMatchingArch K L σ φa fa →
        ∀ I I' : ℂ,
          AutomorphicForm.IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (AutomorphicForm.archHaarL K L) δ τ'
            (φa ∘ AutomorphicForm.archIdentGL K L) I' →
          AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) (AutomorphicForm.archHaarK K) γ τ fa I →
          I' = (-1 : ℂ) ^ (Nat.card {w : NumberField.InfinitePlace K //
            ∀ z : (L ⊗[K] w.Completion)ˣ,
              ¬ AutomorphicForm.IsSigmaConjugate K L w.Completion σ
                  (Matrix.GeneralLinearGroup.map
                    (Algebra.TensorProduct.map (AlgHom.id K L)
                      (Pi.evalAlgHom K (fun w : NumberField.InfinitePlace K => w.Completion) w)).toRingHom δ)
                  (Matrix.GeneralLinearGroup.scalar (Fin 2) z)}) * I := by sorry
