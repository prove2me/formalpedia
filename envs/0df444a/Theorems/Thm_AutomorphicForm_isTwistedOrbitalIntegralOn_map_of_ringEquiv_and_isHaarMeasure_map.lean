-- Prove2me | Theorems.Thm_AutomorphicForm_isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map
-- name    : AutomorphicForm.isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/c16f8dd8-9ae6-5ea6-926e-deb2a68b6e7a
-- title:
--   Transport of twisted orbital integrals along a ring isomorphism
-- statement:
--   Let $K \subseteq L$ be fields with $L$ finite-dimensional over $K$, let $A$ be a commutative topological ring that is a $K$-algebra, and let $\sigma$ be a $K$-algebra automorphism of $L$; let $(K',L',A',\sigma')$ be a second such datum. Let $E : L \otimes_K A \to L' \otimes_{K'} A'$ be a ring isomorphism with $E$ and $E^{-1}$ continuous and with $E \circ (\sigma \otimes \mathrm{id}_A) = (\sigma' \otimes \mathrm{id}_{A'}) \circ E$, let $\mu$ be a measure on $\mathrm{GL}_2(L \otimes_K A)$ for the Borel structure of the topology, and let $\delta \in \mathrm{GL}_2(L \otimes_K A)$. Write $E_*$ for the induced group homomorphism $\mathrm{GL}_2(L \otimes_K A) \to \mathrm{GL}_2(L' \otimes_{K'} A')$ obtained by applying $E$ entrywise, and $\sigma_{\mathrm{GL}}$ for the entrywise action of $\sigma \otimes \mathrm{id}_A$; the twisted centraliser of $\delta$ is the subgroup $\{t : t\,\delta\,\sigma_{\mathrm{GL}}(t)^{-1} = \delta\}$, carrying its Borel structure, and similarly for $E_*\delta$ on the primed side. Three assertions are made. First, for all measures $\tau'$ on the twisted centraliser of $\delta$ and $\tau''$ on that of $E_*\delta$ whose pushforwards to $\mathrm{GL}_2(L' \otimes_{K'} A')$ agree, the first along the inclusion and the second along $t \mapsto E_*(t)$: for every $\varphi : \mathrm{GL}_2(L \otimes_K A) \to \mathbb{C}$ and $I \in \mathbb{C}$, if $I$ is a twisted orbital integral for $(\mu, \delta, \tau', \varphi)$ — that is, there is a non-negative Borel measurable $w$ with compact support such that $\int w(tx)\,d\tau'(t) = 1$ for every $x$ with $\varphi(x^{-1}\delta\,\sigma_{\mathrm{GL}}(x)) \neq 0$, and $I = \int \varphi(x^{-1}\delta\,\sigma_{\mathrm{GL}}(x))\,w(x)\,d\mu(x)$ — then the same $I$ is a twisted orbital integral for $((E_*)_*\mu,\ E_*\delta,\ \tau'',\ \varphi \circ (E^{-1})_*)$ on the primed side; only this implication is asserted, not the converse. Second, if $\mu$ is a Haar measure then so is $(E_*)_*\mu$. Third, every Haar measure $\tau''$ on the twisted centraliser of $E_*\delta$ arises, in the above sense of matching pushforwards, from some Haar measure $\tau'$ on the twisted centraliser of $\delta$.
--
--   This is the transport lemma that lets twisted orbital integrals, the ambient Haar measure and the Haar measures on twisted centralisers be carried along a bicontinuous base-change isomorphism intertwining the two twists, so that a local computation may be performed in whichever model of $L \otimes_K A$ is convenient. It is used in the archimedean comparison of twisted and untwisted orbital integrals and in the resulting matching statement for central transfers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isTwistedOrbitalIntegralOn_map_of_ringEquiv_and_isHaarMeasure_map
    {K L A : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)
    {K' L' A' : Type} [Field K'] [Field L'] [Algebra K' L'] [FiniteDimensional K' L']
    [CommRing A'] [Algebra K' A'] [TopologicalSpace A'] [IsTopologicalRing A'] (σ' : L' ≃ₐ[K'] L')
    (E : L ⊗[K] A ≃+* L' ⊗[K'] A') (hE : Continuous E) (hE' : Continuous E.symm)
    (hEσ : ∀ z, E (sigmaTensor K L A σ z) = sigmaTensor K' L' A' σ' (E z))
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (glBorelOf (L ⊗[K] A)))
    (δ : GL (Fin 2) (L ⊗[K] A)) :
    (∀ (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
        (τ'' : @Measure (twistedCentralizer K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ))
          (twistedCentralizerBorel K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ))),
        (letI := glBorelOf (L' ⊗[K'] A'); letI := twistedCentralizerBorel K L A σ δ;
          letI := twistedCentralizerBorel K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ);
          Measure.map (fun t : twistedCentralizer K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ) =>
              (t : GL (Fin 2) (L' ⊗[K'] A'))) τ'' =
            Measure.map (fun t : twistedCentralizer K L A σ δ =>
              Matrix.GeneralLinearGroup.map E.toRingHom (t : GL (Fin 2) (L ⊗[K] A))) τ') →
        ∀ (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (I : ℂ),
          IsTwistedOrbitalIntegralOn K L A σ μ δ τ' φ I →
          IsTwistedOrbitalIntegralOn K' L' A' σ'
            (@Measure.map _ _ (glBorelOf (L ⊗[K] A)) (glBorelOf (L' ⊗[K'] A'))
              (Matrix.GeneralLinearGroup.map E.toRingHom) μ)
            (Matrix.GeneralLinearGroup.map E.toRingHom δ) τ''
            (φ ∘ Matrix.GeneralLinearGroup.map E.symm.toRingHom) I) ∧
    (@Measure.IsHaarMeasure _ _ _ (glBorelOf (L ⊗[K] A)) μ →
      @Measure.IsHaarMeasure _ _ _ (glBorelOf (L' ⊗[K'] A'))
        (@Measure.map _ _ (glBorelOf (L ⊗[K] A)) (glBorelOf (L' ⊗[K'] A'))
          (Matrix.GeneralLinearGroup.map E.toRingHom) μ)) ∧
    (∀ τ'' : @Measure (twistedCentralizer K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ))
        (twistedCentralizerBorel K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ)),
      @Measure.IsHaarMeasure _ _ _
        (twistedCentralizerBorel K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ)) τ'' →
      ∃ τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ),
        @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel K L A σ δ) τ' ∧
        (letI := glBorelOf (L' ⊗[K'] A'); letI := twistedCentralizerBorel K L A σ δ;
          letI := twistedCentralizerBorel K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ);
          Measure.map (fun t : twistedCentralizer K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ) =>
              (t : GL (Fin 2) (L' ⊗[K'] A'))) τ'' =
            Measure.map (fun t : twistedCentralizer K L A σ δ =>
              Matrix.GeneralLinearGroup.map E.toRingHom (t : GL (Fin 2) (L ⊗[K] A))) τ')) := by sorry
