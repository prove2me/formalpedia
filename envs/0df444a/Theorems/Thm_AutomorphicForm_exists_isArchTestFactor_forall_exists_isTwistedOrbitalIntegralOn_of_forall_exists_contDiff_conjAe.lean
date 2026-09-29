-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isArchTestFactor_forall_exists_isTwistedOrbitalIntegralOn_of_forall_exists_contDiff_conjAe
-- name    : AutomorphicForm.exists_isArchTestFactor_forall_exists_isTwistedOrbitalIntegralOn_of_forall_exists_contDiff_conjAe
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/95a21bda-7de7-5fb0-95be-a17e60f61d6b
-- title:
--   Archimedean base-change transfer from a ramified real place
-- statement:
--   Let $K \subseteq L$ be number fields with $\operatorname{finrank}_K L = 2$, let $\sigma$ be a non-trivial $K$-algebra automorphism of $L$, and assume there is no $K$-algebra map $L \to K_\infty$, where $K_\infty$ denotes the infinite adele ring. Let `tysL` be an archimedean type family for $L$ and let $\varphi_a : \mathrm{GL}_2(L_\infty) \to \mathbb{C}$ be an archimedean test factor (compactly supported and of the form $g \mapsto \Phi(\text{archEntries}(g))$ for a smooth $\Phi$ on $2\times 2$ matrices over the mixed space of $L$) which is bi-finite for `tysL`, i.e. $x \mapsto \varphi_a(x^{-1})$ lies in the type-cut submodule and $\varphi_a$ in the dual type-cut submodule attached to `tysL`. The hypothesis `hram` is the parametric transfer over $\mathbb{R}$ with twist by complex conjugation: for every real normed space $P$, Haar measures $\mu_A$ on $\mathrm{GL}_2(\mathbb{R})$ and $\mu_L$ on $\mathrm{GL}_2(\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R})$ (Borel $\sigma$-algebras throughout), and every smooth compactly supported $\Phi : (\mathrm{Mat}_2(\mathbb{C})) \times P \to \mathbb{C}$ whose closed support consists of pairs with invertible first-coordinate determinant and whose right and left translates by `rowIsometrySubgroup₀ ℂ` span a finite-dimensional space, there is a smooth compactly supported $F$ on $\mathrm{Mat}_2(\mathbb{R}) \times P$, again supported over invertible determinants and with finite-dimensional spans of right and left `rowIsometrySubgroup₀ ℝ`-translates, such that every finite linear relation $\sum_j c_j \Phi(E, q_j) = 0$ valid for all complex $E$ forces $\sum_j c_j F(E', q_j) = 0$ for all real $E'$, and such that: for each $p \in P$, each regular semisimple $\gamma \in \mathrm{GL}_2(\mathbb{R})$ (meaning $\operatorname{tr}(\gamma)^2 - 4\det(\gamma)$ is a unit) and each $\delta$ with $\gamma$ mapping, under the base-change embedding, exactly to the norm string $\delta \cdot \sigma(\delta)$ of $\delta$, and each pair of Haar measures $\tau$ on the centraliser of $\gamma$ and $\tau'$ on the conjugation-twisted centraliser of $\delta$ that are coupled (the two push-forwards to $\mathrm{GL}_2(\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R})$ agree), any value $I'$ of the twisted orbital integral of $\Phi(\cdot, p)$ — read through the identification $\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R} \cong \mathbb{C}$ — against $\mu_L, \delta, \tau'$ equals any value $I$ of the orbital integral of $F(\cdot, p)$ against $\mu_A, \gamma, \tau$; and for each $p$ and each regular semisimple $\gamma$ which is the norm of no $\delta$, every value of the orbital integral of $F(\cdot,p)$ is $0$. The conclusion asserts the existence of an archimedean type family `tysK` for $K$ and a function $f_a : \mathrm{GL}_2(K_\infty) \to \mathbb{C}$ which is an archimedean test factor, bi-finite for `tysK`, and such that, with the Haar measures `archHaarK` and `archHaarL`: for every regular semisimple $\gamma \in \mathrm{GL}_2(K_\infty)$, every $\delta \in \mathrm{GL}_2(L \otimes_K K_\infty)$ whose norm string equals the image of $\gamma$, and every coupled pair of Haar measures $\tau, \tau'$ on the centraliser of $\gamma$ and the $\sigma$-twisted centraliser of $\delta$, there is a single $I \in \mathbb{C}$ that is simultaneously a value of the twisted orbital integral of $\varphi_a \circ \text{archIdentGL}$ at $(\delta, \tau')$ and a value of the orbital integral of $f_a$ at $(\gamma, \tau)$; and for every regular semisimple $\gamma$ that is the norm of no $\delta$ and every Haar $\tau$ on its centraliser, the orbital integral of $f_a$ at $(\gamma,\tau)$ takes the value $0$. Note the shape of the two clauses: the matching clause produces one common value, and the vanishing clause asserts that $0$ is a value, rather than that all values vanish.
--
--   This is the archimedean matching of (twisted) orbital integrals for quadratic base change of $\mathrm{GL}(2)$, in the situation where no infinite place of $K$ splits in $L$: the global archimedean transfer from $L$ to $K$ is deduced from a single parametric transfer statement for the extension $\mathbb{C}/\mathbb{R}$ with its conjugation twist. It feeds the construction of the archimedean component of a transferred test function, and is cited by [`AutomorphicForm.exists_isArchTestFactor_forall_isNormConjugator_one_exists_isTwistedOrbitalIntegralOn_of_isEmpty_algHom`](thm.html#AutomorphicForm.exists_isArchTestFactor_forall_isNormConjugator_one_exists_isTwistedOrbitalIntegralOn_of_isEmpty_algHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isArchTestFactor_forall_exists_isTwistedOrbitalIntegralOn_of_forall_exists_contDiff_conjAe.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem
AutomorphicForm.exists_isArchTestFactor_forall_exists_isTwistedOrbitalIntegralOn_of_forall_exists_contDiff_conjAe
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (hι : IsEmpty (L →ₐ[K] InfiniteAdeleRing K)) (tysL : ArchTypeFamily L)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : IsArchTestFactor L φa)
    (hφt : IsArchFactorBiFinite L tysL φa)
    (hram :
      ∀ (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P]
      (μA : @Measure (GL (Fin 2) ℝ) (glBorelOf ℝ))
      (μL : @Measure (GL (Fin 2) (ℂ ⊗[ℝ] ℝ)) (glBorelOf (ℂ ⊗[ℝ] ℝ)))
      (Φ : (Fin 2 → Fin 2 → ℂ) × P → ℂ)
      (hΦs : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦc : HasCompactSupport Φ)
      (hΦU : tsupport Φ ⊆ {q | IsUnit (Matrix.det (Matrix.of q.1))})
      (hΦr : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℂ =>
        fun q : (Fin 2 → Fin 2 → ℂ) × P =>
          Φ (Matrix.of.symm (Matrix.of q.1 * ((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)), q.2))))
      (hΦl : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℂ =>
        fun q : (Fin 2 → Fin 2 → ℂ) × P =>
          Φ (Matrix.of.symm (((k : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) * Matrix.of q.1), q.2))))
      (hμA : @Measure.IsHaarMeasure _ _ _ (glBorelOf ℝ) μA)
      (hμL : @Measure.IsHaarMeasure _ _ _ (glBorelOf (ℂ ⊗[ℝ] ℝ)) μL),
      ∃ F : (Fin 2 → Fin 2 → ℝ) × P → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) F ∧ HasCompactSupport F ∧ tsupport F ⊆ {r | IsUnit (Matrix.det (Matrix.of r.1))} ∧
        FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℝ =>
          fun r : (Fin 2 → Fin 2 → ℝ) × P =>
            F (Matrix.of.symm (Matrix.of r.1 * ((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)), r.2))) ∧
        FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ ℝ =>
          fun r : (Fin 2 → Fin 2 → ℝ) × P =>
            F (Matrix.of.symm (((k : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) * Matrix.of r.1), r.2))) ∧
        (∀ (n : ℕ) (c : Fin n → ℂ) (q : Fin n → P),
          (∀ E : Fin 2 → Fin 2 → ℂ, ∑ j, c j * Φ (E, q j) = 0) →
            ∀ E' : Fin 2 → Fin 2 → ℝ, ∑ j, c j * F (E', q j) = 0) ∧
        (∀ p : P, ∀ γ : GL (Fin 2) ℝ, IsRegularSemisimple γ →
          ∀ δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ), IsNormConjugator ℝ ℂ ℝ Complex.conjAe γ δ 1 →
          ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ))
            (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ)
              (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ)),
            @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
            @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ' →
            Coupled ℝ ℂ ℝ Complex.conjAe γ δ 1 τ τ' →
            ∀ I I' : ℂ,
              IsTwistedOrbitalIntegralOn ℝ ℂ ℝ Complex.conjAe μL δ τ'
                (fun y => Φ (Matrix.of.symm
                  ((Matrix.GeneralLinearGroup.map
                    (@AlgEquiv.toRingEquiv ℝ (ℂ ⊗[ℝ] ℝ) ℂ _ _ _ Algebra.TensorProduct.leftAlgebra _
                      (Algebra.TensorProduct.rid ℝ ℝ ℂ)).toRingHom y : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ),
                  p)) I' →
              IsOrbitalIntegralOn ℝ μA γ τ (fun g => F (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℝ), p)) I →
              I' = I) ∧
        (∀ p : P, ∀ γ : GL (Fin 2) ℝ, IsRegularSemisimple γ → (¬ ∃ δ, IsNormOf ℝ ℂ ℝ Complex.conjAe γ δ) →
          ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) ℝ))) (centralizerBorel ℝ γ),
            @Measure.IsHaarMeasure _ _ _ (centralizerBorel ℝ γ) τ →
            ∀ I : ℂ, IsOrbitalIntegralOn ℝ μA γ τ (fun g => F (Matrix.of.symm (g : Matrix (Fin 2) (Fin 2) ℝ), p)) I →
              I = 0)) :
    ∃ (tysK : ArchTypeFamily K) (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ),
      IsArchTestFactor K fa ∧ IsArchFactorBiFinite K tysK fa ∧
      (∀ γ : GL (Fin 2) (InfiniteAdeleRing K), IsRegularSemisimple γ →
        ∀ δ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K), IsNormConjugator K L (InfiniteAdeleRing K) σ γ δ 1 →
        ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
            (centralizerBorel (InfiniteAdeleRing K) γ))
          (τ' : @Measure (twistedCentralizer K L (InfiniteAdeleRing K) σ δ)
            (twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ)),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel (InfiniteAdeleRing K) γ) τ →
          @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L (InfiniteAdeleRing K) σ δ) τ' →
          Coupled K L (InfiniteAdeleRing K) σ γ δ 1 τ τ' →
          ∃ I : ℂ,
            IsTwistedOrbitalIntegralOn K L (InfiniteAdeleRing K) σ (archHaarL K L) δ τ' (φa ∘ archIdentGL K L) I ∧
              IsOrbitalIntegralOn (InfiniteAdeleRing K) (archHaarK K) γ τ fa I) ∧
      (∀ γ : GL (Fin 2) (InfiniteAdeleRing K), IsRegularSemisimple γ →
        (¬ ∃ δ, IsNormOf K L (InfiniteAdeleRing K) σ γ δ) →
        ∀ τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (InfiniteAdeleRing K))))
            (centralizerBorel (InfiniteAdeleRing K) γ),
          @Measure.IsHaarMeasure _ _ _ (centralizerBorel (InfiniteAdeleRing K) γ) τ →
          IsOrbitalIntegralOn (InfiniteAdeleRing K) (archHaarK K) γ τ fa 0) := by sorry
