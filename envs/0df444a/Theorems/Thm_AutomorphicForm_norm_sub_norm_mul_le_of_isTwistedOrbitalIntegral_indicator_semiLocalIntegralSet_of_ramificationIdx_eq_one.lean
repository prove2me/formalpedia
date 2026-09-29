-- Prove2me | Theorems.Thm_AutomorphicForm_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one
-- name    : AutomorphicForm.norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/a6620181-4288-55df-bcd3-1d8342a63ff2
-- title:
--   Unit fundamental lemma inequality at an unramified place
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, and let $\sigma \in \mathrm{Gal}(L/K)$ be such that every element of the Galois group lies in the subgroup of integer powers of $\sigma$. Let $v$ be a nonzero prime of $\mathcal{O}_K$, and assume that every prime $w'$ of $\mathcal{O}_L$ whose contraction to $\mathcal{O}_K$ is $v$ satisfies $e(w'/v) = 1$. Write $K_v$ for the $v$-adic completion and $E = L \otimes_K K_v$. The assertion is that for every $\delta \in \mathrm{GL}_2(E)$ whose off-diagonal entries $\delta_{10}$ and $\delta_{01}$ vanish and whose diagonal entries satisfy $N_{E/K_v}(\delta_{00}) \neq N_{E/K_v}(\delta_{11})$ (norms taken by `Algebra.norm` over $K_v$), for every Haar measure $\tau'$ on the twisted centraliser $\{t \in \mathrm{GL}_2(E) : t\,\delta\,\sigma(t)^{-1} = \delta\}$ (where $\sigma$ acts entrywise on $E = L \otimes_K K_v$ through `sigmaGL`), equipped with its Borel $\sigma$-algebra, normalised so that the part of the centraliser lying in the integral set $\mathcal{K} = \{g \in \mathrm{GL}_2(E) : g$ and $g^{-1}$ have entries in the image of $\mathcal{O}_L \otimes_{\mathcal{O}_K} \mathcal{O}_{K_v}\}$ has measure $1$, and for every $I \in \mathbb{C}$ that is a twisted orbital integral of the indicator function of $\mathcal{K}$ at $\delta$ — that is, $I = \int \mathbf{1}_{\mathcal{K}}(x^{-1}\delta\,\sigma(x))\, w(x)\, d\mu(x)$ for some weight function $w$ satisfying `IsTwistedSectionFnOn` for $\tau'$, with $\mu$ the Haar measure on $\mathrm{GL}_2(E)$ normalised by the compacts of $\mathcal{K}$ — one has $$\|N(\delta_{00}) - N(\delta_{11})\| \cdot \|I\| \le \|N(\delta_{00})\, N(\delta_{11})\|^{1/2},$$ the norms on the left and right being $v$-adic norms on $K_v$ and $\|I\|$ the complex absolute value.
--
--   This is the unit case of the fundamental lemma for cyclic base change of $\mathrm{GL}_2$ at a place unramified in $L/K$, stated for a regular diagonal twisted-conjugacy representative and in inequality form with constant exactly $1$, so that it may be multiplied over cofinitely many places. It is used in the proof of [`AutomorphicForm.exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure`](thm.html#AutomorphicForm.exists_forall_lintegral_orbital_doubleCoset_le_mul_prod_rpow_measure), where bounds of this shape at all finite places are combined into a global estimate for hyperbolic terms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct Pointwise

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w' : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w' = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w').asIdeal w'.asIdeal = 1) :
    ∀ (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
      (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 0 = 0 → (δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 1 = 0 →
      Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) ≠
        Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1) →
    ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)
        (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ)),
      @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ) τ' →
      τ' (Subtype.val ⁻¹' AutomorphicForm.semiLocalIntegralSet K L v) = 1 →
    ∀ I : ℂ, AutomorphicForm.IsTwistedOrbitalIntegral K L v σ δ τ'
        ((AutomorphicForm.semiLocalIntegralSet K L v).indicator (fun _ => (1 : ℂ))) I →
      ‖Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) -
          Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)‖ * ‖I‖ ≤
        ‖Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 0 0) *
              Algebra.norm (v.adicCompletion K) ((δ : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) 1 1)‖ ^ ((1 : ℝ) / 2) := by sorry
