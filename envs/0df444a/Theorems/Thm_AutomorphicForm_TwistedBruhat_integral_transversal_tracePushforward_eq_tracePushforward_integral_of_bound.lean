-- Prove2me | Theorems.Thm_AutomorphicForm_TwistedBruhat_integral_transversal_tracePushforward_eq_tracePushforward_integral_of_bound
-- name    : AutomorphicForm.TwistedBruhat.integral_transversal_tracePushforward_eq_tracePushforward_integral_of_bound
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/d5aa0725-e232-5166-8c28-64189aaf6ae0
-- title:
--   Fubini interchange of trace push-forward with transversal integrals
-- statement:
--   Let $L/K$ be a Galois extension of number fields, let $\nu$ be a Haar measure on the idele group $\mathbb{A}_L^\times$, let $D$ be an idele Galois descent datum for $L/K$ (a homomorphism from $\mathrm{Gal}(L/K)$ to ring automorphisms of $\mathbb{A}_L$, compatible with $L \to \mathbb{A}_L$ and continuous), let $\sigma \in \mathrm{Gal}(L/K)$, let $\xi$ be a homomorphism from the full subgroup of $\mathbb{A}_L^\times$ to $\mathbb{C}^\times$ whose associated scalar function is continuous, let $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$, and let $\tau$ be a measure on $\mathbb{A}_L^\times$, for the Borel structure on ideles, which is finite on compact sets. Write $n = \dim_K \ker(\mathrm{Tr}_{L/K})$, let $\Phi(r,w')\in\mathbb{A}_L$ be the trace-adapted transversal coordinate `traceFibre` (the combination $\beta(r)/[L:K] + \sum_i \beta(w'_i)e_i$ with $e_i$ the chosen basis of $\ker \mathrm{Tr}_{L/K}$), and set $$G(t,k,\zeta,r,w') = \varphi\bigl(k^{-1}\,n(\Phi(r,w')t^{-1})\,\mathrm{diag}(\sigma_D(t)t^{-1},1)\,z(\sigma_D(\zeta))\,\sigma_D(k)\bigr),$$ where $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$, $z$ is the central scalar embedding, $\sigma_D$ denotes the action of $\sigma$ through $D$ on ideles and, entrywise, on matrices, and $k$ runs over the subgroup of $\mathrm{GL}_2(\mathbb{A}_L)$ of elements with integral finite part and row-isometric archimedean components. Assume, as a single grouped hypothesis, that there are compact sets $C_t, C_\zeta \subseteq \mathbb{A}_L^\times$, $C_r \subseteq \mathbb{A}_K$, $C_w \subseteq \mathbb{A}_K^{\,n}$ and $M \ge 0$ with: $\lVert G \rVert \le M$ everywhere; $G = 0$ whenever $\zeta \notin C_\zeta$; for $\tau$-almost every $t \notin C_t$, $G = 0$ for all remaining arguments; for $t \in C_t$, $G = 0$ whenever $r \notin C_r$ or $w' \notin C_w$; and $G$ is continuous as a function on the product of the five domains. Then for every $r \in \mathbb{A}_K$ the iterated lower integral, over $\zeta$ against $\nu$, then $k$ against the Haar measure of the maximal compact subgroup, then $t$ against $\tau$, of the extended norm of $\xi(\zeta)$ times the trace push-forward at $r$ of $w \mapsto G$-with-$\Phi(r,w')$ replaced by $w$ is finite, and the corresponding iterated Bochner integral of $\xi(\zeta)$ times that trace push-forward equals the trace push-forward at $r$ of the function sending $w$ to the iterated integral $\int\!\int\!\int \xi(\zeta)\,\varphi(k^{-1}n(wt^{-1})\mathrm{diag}(\sigma_D(t)t^{-1},1)z(\sigma_D(\zeta))\sigma_D(k))$ in the same order; here the trace push-forward of $F$ at $r$ is $\int F(\Phi(r,w'))\,dw'$ against the product adelic Haar measure on $\mathbb{A}_K^{\,n}$.
--
--   This is the Fubini–Tonelli interchange step for the twisted Bruhat computation: it licenses moving the integration along the fibres of the trace past the integrations over the transversal parameter $t$, the maximal compact subgroup and the central ideles, the compact-support and boundedness hypotheses being exactly those produced by the support analysis of the unipotent-type integrand. It is used in the pointwise identification of the transversal pieces of the twisted orbital expression with a product of local factors at unramified places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TwistedBruhat_integral_transversal_tracePushforward_eq_tracePushforward_integral_of_bound.lean

import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_AutomorphicForm_TransversalMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.AdelicTracePushforward
open scoped TensorProduct Pointwise ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.TwistedBruhat.integral_transversal_tracePushforward_eq_tracePushforward_integral_of_bound
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (φ : AdelicGL2 (𝓞 L) L → ℂ)
    (τj : @Measure (AdeleRing (𝓞 L) L)ˣ (NumberField.Idele.ideleBorel L)) (hτfin : IsFiniteMeasureOnCompacts τj)
    (Ct : Set (AdeleRing (𝓞 L) L)ˣ) (Cz : Set (AdeleRing (𝓞 L) L)ˣ) (Cr : Set (AdeleRing (𝓞 K) K))
    (Cw : Set (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K)) (M : ℝ)
    (hsupp : IsCompact Ct ∧ IsCompact Cz ∧ IsCompact Cr ∧ IsCompact Cw ∧ 0 ≤ M ∧
      (∀ (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
          (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K),
        ‖φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
              unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
              diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
              centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
              AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))‖ ≤ M) ∧
      (∀ (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
          (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K),
        ζ ∉ Cz → φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
              unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
              diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
              centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
              AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) = 0) ∧
      (∀ᵐ t ∂τj, t ∉ Ct → ∀ (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
          (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K),
        φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
              unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
              diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
              centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
              AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) = 0) ∧
      (∀ t ∈ Ct, ∀ (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
          (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K),
        (r ∉ Cr ∨ w' ∉ Cw) → φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
              unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
              diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
              centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
              AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L)) = 0) ∧
      Continuous (fun p : ((AdeleRing (𝓞 L) L)ˣ × ↥(adelicMaximalCompact L)) ×
          ((AdeleRing (𝓞 L) L)ˣ × (AdeleRing (𝓞 K) K ×
            (Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K))) =>
        (fun (t : (AdeleRing (𝓞 L) L)ˣ) (k : adelicMaximalCompact L) (ζ : (AdeleRing (𝓞 L) L)ˣ)
            (r : AdeleRing (𝓞 K) K) (w' : Fin (Module.finrank K (LinearMap.ker (Algebra.trace K L))) → AdeleRing (𝓞 K) K) =>
          φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
              unipotentGL2 ((traceFibre K L r w') * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
              diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
              centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
              AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2))
    (r : AdeleRing (𝓞 K) K) :
    (∫⁻ t, ∫⁻ k, ∫⁻ ζ, ‖((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
          tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r‖ₑ ∂νZL ∂(maximalCompactHaar L) ∂τj) ≠ ⊤ ∧
    (∫ t, ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
          tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂νZL) ∂(maximalCompactHaar L) ∂τj) =
      tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
        ∫ t, ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) *
          (φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) ∂νZL) ∂(maximalCompactHaar L) ∂τj) r := by sorry
