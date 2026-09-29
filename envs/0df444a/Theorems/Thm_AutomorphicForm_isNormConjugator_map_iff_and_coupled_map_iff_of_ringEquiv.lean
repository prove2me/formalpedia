-- Prove2me | Theorems.Thm_AutomorphicForm_isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv
-- name    : AutomorphicForm.isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/a4eba7f2-97db-526c-944e-184e6a1d58ed
-- title:
--   Transport of norm-conjugators and coupled measures along ring isomorphisms
-- statement:
--   Let $K \subseteq L$ be a finite extension of fields, $A$ a commutative topological ring that is a $K$-algebra, and $\sigma$ a $K$-algebra automorphism of $L$; let $K' \subseteq L'$, $A'$, $\sigma'$ be a second such package, with $[L:K] = [L':K']$. Assume given a ring isomorphism $e : A \to A'$ with $e$ and $e^{-1}$ continuous, and a ring isomorphism $E : L \otimes_K A \to L' \otimes_{K'} A'$ with $E$ and $E^{-1}$ continuous, such that $E$ intertwines $\sigma \otimes \mathrm{id}_A$ with $\sigma' \otimes \mathrm{id}_{A'}$, and such that for every $g \in \mathrm{GL}_2(A)$ the entrywise image under $E$ of the image of $g$ under $\mathrm{GL}_2(A) \to \mathrm{GL}_2(L \otimes_K A)$ (induced by $a \mapsto 1 \otimes a$) equals the image of $e_*g$ under $\mathrm{GL}_2(A') \to \mathrm{GL}_2(L' \otimes_{K'} A')$. Fix $\gamma \in \mathrm{GL}_2(A)$ and $\delta, y \in \mathrm{GL}_2(L \otimes_K A)$, and write $e_*$, $E_*$ for the induced maps on $\mathrm{GL}_2$. The conclusion is a conjunction of two assertions. First, the norm-conjugator relation is preserved in both directions: $1 \otimes \gamma = y^{-1} \bigl(\prod_{i=0}^{[L:K]-1} (\sigma \otimes \mathrm{id})^{i}(\delta)\bigr) y$ holds if and only if the corresponding identity $1 \otimes e_*\gamma = (E_*y)^{-1}\bigl(\prod_{i=0}^{[L':K']-1}(\sigma' \otimes \mathrm{id})^{i}(E_*\delta)\bigr)(E_*y)$ holds, the products being taken in increasing order of $i$. Second, for all measures $\tau$ on the centraliser of $\gamma$ in $\mathrm{GL}_2(A)$, $\tau_0$ on the centraliser of $e_*\gamma$ in $\mathrm{GL}_2(A')$, $\tau'$ on the twisted centraliser $\{t : t\,\delta\,((\sigma \otimes \mathrm{id})t)^{-1} = \delta\}$ and $\tau_0'$ on the twisted centraliser of $E_*\delta$ for $\sigma' \otimes \mathrm{id}$ (all carrying the Borel structures induced from the relevant general linear groups), if the pushforward of $\tau_0$ to $\mathrm{GL}_2(A')$ along the inclusion coincides with the pushforward of $\tau$ along $t \mapsto e_*t$, and likewise the pushforward of $\tau_0'$ to $\mathrm{GL}_2(L' \otimes_{K'} A')$ along the inclusion coincides with the pushforward of $\tau'$ along $t \mapsto E_*t$, then the coupling condition for $(\gamma, \delta, y, \tau, \tau')$ — that the pushforward of $\tau'$ along $t \mapsto y^{-1} t y$ equals the pushforward of $\tau$ along $t \mapsto 1 \otimes t$ — holds if and only if the coupling condition for $(e_*\gamma, E_*\delta, E_*y, \tau_0, \tau_0')$ holds.
--
--   This is the transport statement for the two side conditions entering the comparison of twisted orbital integrals on $\mathrm{GL}_2$ over a base change $L/K$ with ordinary orbital integrals over $K$: norm-conjugacy of $\gamma$ with $\delta$ and the compatibility (coupling) of the measures chosen on the centraliser and the twisted centraliser are unchanged when the coefficient ring and its base change are replaced by topologically isomorphic ones along maps compatible with the twist and with the inclusion. It is used in the archimedean matching and twisted-orbital-integral identities for scalar elements proved elsewhere in the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isNormConjugator_map_iff_and_coupled_map_iff_of_ringEquiv
    {K L A : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A] (σ : L ≃ₐ[K] L)
    {K' L' A' : Type} [Field K'] [Field L'] [Algebra K' L'] [FiniteDimensional K' L']
    [CommRing A'] [Algebra K' A'] [TopologicalSpace A'] [IsTopologicalRing A'] (σ' : L' ≃ₐ[K'] L')
    (hrank : Module.finrank K L = Module.finrank K' L')
    (e : A ≃+* A') (he : Continuous e) (he' : Continuous e.symm)
    (E : L ⊗[K] A ≃+* L' ⊗[K'] A') (hE : Continuous E) (hE' : Continuous E.symm)
    (hEσ : ∀ z, E (sigmaTensor K L A σ z) = sigmaTensor K' L' A' σ' (E z))
    (hEe : ∀ g : GL (Fin 2) A, Matrix.GeneralLinearGroup.map E.toRingHom (toTensorGL K L A g) =
      toTensorGL K' L' A' (Matrix.GeneralLinearGroup.map e.toRingHom g))
    (γ : GL (Fin 2) A) (δ y : GL (Fin 2) (L ⊗[K] A)) :
    (IsNormConjugator K L A σ γ δ y ↔
      IsNormConjugator K' L' A' σ' (Matrix.GeneralLinearGroup.map e.toRingHom γ)
        (Matrix.GeneralLinearGroup.map E.toRingHom δ) (Matrix.GeneralLinearGroup.map E.toRingHom y)) ∧
    ∀ (τ : @Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) A))) (centralizerBorel A γ))
      (τ₀ : @Measure (Subgroup.centralizer
          ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) A')))
        (centralizerBorel A' (Matrix.GeneralLinearGroup.map e.toRingHom γ)))
      (τ' : @Measure (twistedCentralizer K L A σ δ) (twistedCentralizerBorel K L A σ δ))
      (τ₀' : @Measure (twistedCentralizer K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ))
        (twistedCentralizerBorel K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ))),
      (letI := glBorelOf A'; letI := centralizerBorel A γ;
        letI := centralizerBorel A' (Matrix.GeneralLinearGroup.map e.toRingHom γ);
        Measure.map (fun t : Subgroup.centralizer
            ({Matrix.GeneralLinearGroup.map e.toRingHom γ} : Set (GL (Fin 2) A')) => (t : GL (Fin 2) A')) τ₀ =
          Measure.map (fun t : Subgroup.centralizer ({γ} : Set (GL (Fin 2) A)) =>
            Matrix.GeneralLinearGroup.map e.toRingHom (t : GL (Fin 2) A)) τ) →
      (letI := glBorelOf (L' ⊗[K'] A'); letI := twistedCentralizerBorel K L A σ δ;
        letI := twistedCentralizerBorel K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ);
        Measure.map (fun t : twistedCentralizer K' L' A' σ' (Matrix.GeneralLinearGroup.map E.toRingHom δ) =>
            (t : GL (Fin 2) (L' ⊗[K'] A'))) τ₀' =
          Measure.map (fun t : twistedCentralizer K L A σ δ =>
            Matrix.GeneralLinearGroup.map E.toRingHom (t : GL (Fin 2) (L ⊗[K] A))) τ') →
      (Coupled K L A σ γ δ y τ τ' ↔
        Coupled K' L' A' σ' (Matrix.GeneralLinearGroup.map e.toRingHom γ)
          (Matrix.GeneralLinearGroup.map E.toRingHom δ) (Matrix.GeneralLinearGroup.map E.toRingHom y) τ₀ τ₀') := by sorry
