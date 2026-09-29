-- Prove2me | Theorems.Thm_AutomorphicForm_exists_gram_map_of_ringEquiv_of_exists_gram
-- name    : AutomorphicForm.exists_gram_map_of_ringEquiv_of_exists_gram
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/440970c1-adec-5863-a13a-a41ff6a5fddb
-- title:
--   Transport of the Gram normalisation along a ring isomorphism
-- statement:
--   Fix fields $K,L$ with $L/K$ finite, a commutative topological $K$-algebra $A$, a $K$-automorphism $\sigma$ of $L$, and primed data $K',L',A',\sigma'$ of the same shape, together with real algebra structures on $L\otimes_K A$ and $L'\otimes_{K'}A'$. Let $e:A\simeq A'$ and $E:L\otimes_K A\simeq L'\otimes_{K'}A'$ be ring isomorphisms with $e,e^{-1},E,E^{-1}$ continuous, such that $E$ intertwines $\sigma\otimes\mathrm{id}$ with $\sigma'\otimes\mathrm{id}$, satisfies $E(1\otimes x)=1\otimes e(x)$, and is $\mathbb{R}$-homogeneous. Let $\gamma\in\mathrm{GL}_2(A)$, $\delta\in\mathrm{GL}_2(L\otimes_K A)$ and let $\gamma',\delta'$ be their images under the maps induced by $e$, $E$. Let $\tau,\tau_0$ be measures on the centralisers of $\gamma,\gamma'$ and $\tau',\tau_0'$ measures on the twisted centralisers $\{t\mid t\delta(\sigma t)^{-1}=\delta\}$ of $\delta,\delta'$, all with Borel structures, and assume $\tau_0,\tau_0'$ push forward into $\mathrm{GL}_2$ to the pushforwards of $\tau,\tau'$ along $e$, $E$. Assume the Gram rule on the unprimed side: there exist $n_1,n_2$, $\mathbb{R}$-linearly independent families $e_1,e_2$ in $M_2(L\otimes_K A)$ spanning respectively the image of $M_2(A)$ under $x\mapsto 1\otimes x$ and $\{X\mid X\delta=\delta\,(\sigma X)\}$, and $s\in(0,\infty)$ with the images of $\tau$ and $\tau'$ in $M_2(L\otimes_K A)$ equal to $s$ times $\sqrt{|\det(\mathrm{Tr}_{\mathbb{R}}\,\mathrm{tr}(e_ke_l))|}$ times the pushforward of Lebesgue measure along $a\mapsto\sum a_ke_k$, with density $|N_{\mathbb{R}}(\det X)|^{-1}$. Then the same statement holds for the primed data, with $\tau_0,\tau_0'$ and the same scalar $s$.
--
--   This is the transport along an isomorphism of place models of the Gram-type normalisation of Haar measures on a centraliser and a twisted centraliser of $\mathrm{GL}_2$, used to compare measure normalisations at an archimedean place for two isomorphic models of the local data. It feeds the comparison of a twisted orbital integral with an orbital integral up to sign and an explicit archimedean scalar.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_gram_map_of_ringEquiv_of_exists_gram.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_gram_map_of_ringEquiv_of_exists_gram
    {K L A : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)
    {K' L' A' : Type} [Field K'] [Field L'] [Algebra K' L'] [FiniteDimensional K' L']
    [CommRing A'] [Algebra K' A'] [TopologicalSpace A'] [IsTopologicalRing A'] (σ' : L' ≃ₐ[K'] L')
    [Algebra ℝ (L ⊗[K] A)] [Algebra ℝ (L' ⊗[K'] A')]
    (e : A ≃+* A') (he : Continuous e) (he' : Continuous e.symm)
    (E : L ⊗[K] A ≃+* L' ⊗[K'] A') (hE : Continuous E) (hE' : Continuous E.symm)
    (hEσ : ∀ z, E (sigmaTensor K L A σ z) = sigmaTensor K' L' A' σ' (E z))
    (hEι : ∀ x : A, E ((1 : L) ⊗ₜ[K] x) = (1 : L') ⊗ₜ[K'] e x)
    (hEr : ∀ (r : ℝ) (z : L ⊗[K] A), E (r • z) = r • E z)
    (γ : GL (Fin 2) A) (γ' : GL (Fin 2) A') (hγ' : Matrix.GeneralLinearGroup.map e.toRingHom γ = γ')
    (δ : GL (Fin 2) (L ⊗[K] A)) (δ' : GL (Fin 2) (L' ⊗[K'] A'))
    (hδ' : Matrix.GeneralLinearGroup.map E.toRingHom δ = δ')
    (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
    (τ₀ : @Measure (Subgroup.centralizer ({γ'} : Set (GL (Fin 2) A'))) (centralizerBorel A' γ'))
    (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
    (τ₀' : @Measure (twistedCentralizer K' L' A' σ' δ') (twistedCentralizerBorel K' L' A' σ' δ'))
    (hτ₀ : letI := glBorelOf A'; letI := centralizerBorel A γ; letI := centralizerBorel A' γ'
      Measure.map (fun t : Subgroup.centralizer ({γ'} : Set (GL (Fin 2) A')) => (t : GL (Fin 2) A')) τ₀ =
        Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) =>
          Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) A)) τ)
    (hτ₀' : letI := glBorelOf (L' ⊗[K'] A'); letI := twistedCentralizerBorel K L A σ δ;
      letI := twistedCentralizerBorel K' L' A' σ' δ'
      Measure.map (fun t : twistedCentralizer K' L' A' σ' δ' => (t : GL (Fin 2) (L' ⊗[K'] A'))) τ₀' =
        Measure.map (fun t : twistedCentralizer K L A σ δ =>
          Matrix.GeneralLinearGroup.map E.toRingHom (t : GL (Fin 2) (L ⊗[K] A))) τ')
    (hgram : (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) := borel _
       letI := centralizerBorel A γ
       letI := twistedCentralizerBorel K L A σ δ
       ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (L ⊗[K] A))
         (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) (s : ENNReal),
         s ≠ 0 ∧ s ≠ ⊤ ∧
         LinearIndependent ℝ e₁ ∧
           (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) =
             Set.range (fun Y : Matrix (Fin 2) (Fin 2) A =>
               Y.map (fun x : A => ((1 : L) ⊗ₜ[K] x : L ⊗[K] A))) ∧
         LinearIndependent ℝ e₂ ∧
           (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) =
             {X | X * (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) =
               (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] A)) * X.map (sigmaTensor K L A σ)} ∧
         Measure.map (fun t : ↥(Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) =>
             ((t : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A).map
               (fun x : A => ((1 : L) ⊗ₜ[K] x : L ⊗[K] A))) τ =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                   Algebra.trace ℝ (L ⊗[K] A) (Matrix.trace (e₁ i * e₁ j))).det|)) •
                 Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
         Measure.map (fun t : ↥(twistedCentralizer K L A σ δ) =>
             ((t : GL (Fin 2) (L ⊗[K] A)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] A))) τ' =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                   Algebra.trace ℝ (L ⊗[K] A) (Matrix.trace (e₂ i * e₂ j))).det|)) •
                 Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (L ⊗[K] A) =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹))) :
    (letI : MeasurableSpace (Matrix (Fin 2) (Fin 2) (L' ⊗[K'] A')) := borel _;
       letI := centralizerBorel A' γ';
       letI := twistedCentralizerBorel K' L' A' σ' δ';
       ∃ (n₁ n₂ : ℕ) (e₁ : Fin n₁ → Matrix (Fin 2) (Fin 2) (L' ⊗[K'] A'))
         (e₂ : Fin n₂ → Matrix (Fin 2) (Fin 2) (L' ⊗[K'] A')) (s : ENNReal),
         s ≠ 0 ∧ s ≠ ⊤ ∧
         LinearIndependent ℝ e₁ ∧
           (Submodule.span ℝ (Set.range e₁) : Set (Matrix (Fin 2) (Fin 2) (L' ⊗[K'] A'))) =
             Set.range (fun Y : Matrix (Fin 2) (Fin 2) A' =>
               Y.map (fun x : A' => ((1 : L') ⊗ₜ[K'] x : L' ⊗[K'] A'))) ∧
         LinearIndependent ℝ e₂ ∧
           (Submodule.span ℝ (Set.range e₂) : Set (Matrix (Fin 2) (Fin 2) (L' ⊗[K'] A'))) =
             {X | X * (δ' : Matrix (Fin 2) (Fin 2) (L' ⊗[K'] A')) =
               (δ' : Matrix (Fin 2) (Fin 2) (L' ⊗[K'] A')) * X.map (sigmaTensor K' L' A' σ')} ∧
         Measure.map (fun t : ↥(Subgroup.centralizer ({γ'} : Set (GL (Fin 2) A'))) =>
             ((t : GL (Fin 2) A') : Matrix (Fin 2) (Fin 2) A').map
               (fun x : A' => ((1 : L') ⊗ₜ[K'] x : L' ⊗[K'] A'))) τ₀ =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₁ =>
                   Algebra.trace ℝ (L' ⊗[K'] A') (Matrix.trace (e₁ i * e₁ j))).det|)) •
                 Measure.map (fun a : Fin n₁ → ℝ => ∑ i, a i • e₁ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (L' ⊗[K'] A') =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹) ∧
         Measure.map (fun t : ↥(twistedCentralizer K' L' A' σ' δ') =>
             ((t : GL (Fin 2) (L' ⊗[K'] A')) : Matrix (Fin 2) (Fin 2) (L' ⊗[K'] A'))) τ₀' =
           s • ((ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j : Fin n₂ =>
                   Algebra.trace ℝ (L' ⊗[K'] A') (Matrix.trace (e₂ i * e₂ j))).det|)) •
                 Measure.map (fun a : Fin n₂ → ℝ => ∑ i, a i • e₂ i) volume).withDensity
               (fun X : Matrix (Fin 2) (Fin 2) (L' ⊗[K'] A') =>
                 (ENNReal.ofReal |Algebra.norm ℝ (Matrix.det X)|)⁻¹)) := by sorry
