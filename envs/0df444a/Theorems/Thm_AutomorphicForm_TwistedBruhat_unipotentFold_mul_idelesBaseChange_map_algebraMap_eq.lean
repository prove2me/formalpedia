-- Prove2me | Theorems.Thm_AutomorphicForm_TwistedBruhat_unipotentFold_mul_idelesBaseChange_map_algebraMap_eq
-- name    : AutomorphicForm.TwistedBruhat.unipotentFold_mul_idelesBaseChange_map_algebraMap_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/3ae35f90-9f5c-57dc-ae2a-46fa0c13d200
-- title:
--   Invariance of the twisted Bruhat fold under K^×
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ Galois, let $\nu_{Z,L}$ be a Haar measure on the idele group $(\mathbb{A}_L)^\times$ (taken with its Borel structure), let $D$ be an idele Galois descent datum for $L/K$, that is a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$ which is continuous and compatible with the embedding of $L$, let $\sigma \in \mathrm{Gal}(L/K)$, let $\xi_L$ be a homomorphism from the full subgroup $\top \le (\mathbb{A}_L)^\times$ to $\mathbb{C}^\times$, let $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$, let $R \in \mathbb{R}$ and let $\mu_K$ be an additive Haar measure on $\mathbb{A}_K$. For an idele $s \in (\mathbb{A}_L)^\times$, an element $k$ of the adelic maximal compact subgroup of $\mathrm{GL}_2(\mathbb{A}_L)$ (those matrices whose finite part is integral and whose archimedean components are row isometries) and $\zeta \in (\mathbb{A}_L)^\times$, put $$G_{s,k,\zeta}(w) = \varphi\bigl(k^{-1}\, n(w s^{-1})\, \mathrm{diag}(\sigma_D(s)s^{-1},1)\, z(\sigma_D(\zeta))\, \sigma_D(k)\bigr),$$ where $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$, $\mathrm{diag}(a,1)$ is `diagOne`, $z$ is the central scalar embedding, $\sigma_D$ denotes the action of $\sigma$ through $D$ on ideles and, entrywise, on $\mathrm{GL}_2(\mathbb{A}_L)$, and set $$F(s) = \int_{\mathbf{K}} \Bigl(\int \xi_L(\zeta)\Bigl(\textstyle\sum^{f}_{\eta \in K^\times} (G_{s,k,\zeta})^\flat(\eta) - \mathbf{1}_{e^R < \mathrm{ht}_L(\mathrm{diag}(s,1))}\int (G_{s,k,\zeta})^\flat \, d\mu_K\Bigr)\,d\nu_{Z,L}(\zeta)\Bigr)\,\mathrm{ideleNorm}_L(s)^{-1}\,dk,$$ the $k$-integral being against the Haar measure `maximalCompactHaar L`, $(\cdot)^\flat =$ `tracePushforward K L` the fibrewise integral along the trace fibration $\mathbb{A}_L \to \mathbb{A}_K$, $\eta$ read in $\mathbb{A}_K$ via the principal embedding, the sum being a `finsum` over $K^\times$, $\mathrm{ht}_L$ the adelic height (product of archimedean and finite heights) and $\mathrm{ideleNorm}_L$ the module character of $\mathbb{A}_L$. The assertion is that for every $q \in K^\times$ and every $t \in (\mathbb{A}_L)^\times$ one has $F(t\cdot \mathrm{bc}(q)) = F(t)$, where $\mathrm{bc}(q)$ is the image in $(\mathbb{A}_L)^\times$, under the base-change map induced by $\mathbb{A}_K \to \mathbb{A}_L$, of the principal idele of $q$.
--
--   This is the $K^\times$-invariance, in the idele variable $t$, of the twisted Bruhat-cell contribution (truncated at height $e^R$) occurring in the $\sigma$-twisted trace computation for $\mathrm{GL}_2$ over $L/K$. It is what allows the $t$-integral to be replaced by an integral over a transversal for $K^\times$, and is used in [`AutomorphicForm.TwistedBruhat.integrableOn_and_integral_finsum_tracePushforward_sub_eq_sum_mul_setIntegral_rankOne_of_transversal`](thm.html#AutomorphicForm.TwistedBruhat.integrableOn_and_integral_finsum_tracePushforward_sub_eq_sum_mul_setIntegral_rankOne_of_transversal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_TwistedBruhat_unipotentFold_mul_idelesBaseChange_map_algebraMap_eq.lean

import Definitions.Def_AutomorphicForm_TwistedCuspKernel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_AdelicTracePushforward
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_NumberField_AdelicHeight

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.AdelicTracePushforward
open scoped TensorProduct Pointwise ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.TwistedBruhat.unipotentFold_mul_idelesBaseChange_map_algebraMap_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ] (νZL : Measure (AdeleRing (𝓞 L) L)ˣ)
    [νZL.IsHaarMeasure]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (R : ℝ)
    [MeasurableSpace (AdeleRing (𝓞 K) K)] [BorelSpace (AdeleRing (𝓞 K) K)]
    (μK : Measure (AdeleRing (𝓞 K) K)) [μK.IsAddHaarMeasure] :
    ∀ (q : Kˣ) (t : (AdeleRing (𝓞 L) L)ˣ),
      (∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * (((t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q))⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q)) * (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q))⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q)) : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * (((t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q))⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q)) * (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q))⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0)) ∂νZL) *
          (((NumberField.TateGlobal.ideleNorm L (t * AutomorphicForm.TransversalMeasure.idelesBaseChange K L
            (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) q)))⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L)) =
      ∫ k, (∫ ζ, ((ξL ⟨ζ, Subgroup.mem_top ζ⟩ : ℂˣ) : ℂ) * ((∑ᶠ η : Kˣ, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) (algebraMap K (AdeleRing (𝓞 K) K) (η : K))) -
                (if Real.exp R < NumberField.AdelicHeight.adelicHeight L (diagOne t : AdelicGL2 (𝓞 L) L) then
                  ∫ r, tracePushforward K L (fun w : AdeleRing (𝓞 L) L =>
                  φ ((k : AdelicGL2 (𝓞 L) L)⁻¹ *
                    unipotentGL2 (w * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
                    diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
                    centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
                    AutomorphicForm.sigmaAdelicAct K L D σ (k : AdelicGL2 (𝓞 L) L))) r ∂μK else 0)) ∂νZL) *
          (((NumberField.TateGlobal.ideleNorm L t)⁻¹ : ℝ) : ℂ)
        ∂(maximalCompactHaar L) := by sorry
