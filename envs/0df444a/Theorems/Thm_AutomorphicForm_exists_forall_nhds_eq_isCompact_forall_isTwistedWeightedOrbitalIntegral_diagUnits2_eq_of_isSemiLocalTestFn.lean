-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_nhds_eq_isCompact_forall_isTwistedWeightedOrbitalIntegral_diagUnits2_eq_of_isSemiLocalTestFn
-- name    : AutomorphicForm.exists_forall_nhds_eq_isCompact_forall_isTwistedWeightedOrbitalIntegral_diagUnits2_eq_of_isSemiLocalTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/124e361b-a785-5a0f-96ff-e397ef11340d
-- title:
--   A single function computes twisted weighted orbital integrals off t=1
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ finite Galois, let $\sigma$ be a $K$-automorphism of $L$ such that every element of $\mathrm{Gal}(L/K)$ is an integral power of $\sigma$, and assume $[L:K]$ is prime. Fix a nonzero prime $v$ of $\mathcal O_K$, write $K_v$ for the completion and $E=L\otimes_K K_v$, and let $\varphi:\mathrm{GL}_2(E)\to\mathbb C$ be a semi-local test function, i.e. locally constant with compact support. The assertion is the existence of a function $\Phi:K_v^\times\times K_v^\times\to\mathbb C$ with three properties. First, at every point $p$ with $p_2\neq 1$ there is a neighbourhood of $p$ on which $\Phi$ is constant. Secondly, there is a compact set $S\subseteq K_v^\times\times K_v^\times$ containing every pair $(a,t)$ with $t\neq 1$ and $\Phi(a,t)\neq 0$. Thirdly, for all $a,t\in K_v^\times$ with $t\neq 1$: (i) for all units $\alpha,\beta$ of $E$ such that the norm string $\prod_{i<[L:K]}\sigma^i(\mathrm{diag}(\alpha,\beta))$, formed with the map induced on $\mathrm{GL}_2$ by $\sigma\otimes\mathrm{id}$, equals the image of $\mathrm{diag}(a,at)$ under base change $\mathrm{GL}_2(K_v)\to\mathrm{GL}_2(E)$, for every measure $\tau'$ on the $\sigma$-twisted centraliser $\{x : x\,\delta\,\sigma(x)^{-1}=\delta\}$ of $\delta=\mathrm{diag}(\alpha,\beta)$, taken with the Borel structure of the subgroup, which is a Haar measure and assigns mass $1$ to the set of its elements lying in the semi-local integral set (those $g$ with $g$ and $g^{-1}$ having entries in the image of $\mathcal O_L\otimes\mathcal O_{K_v}$), and for every $J'\in\mathbb C$ that is a value of the twisted weighted orbital integral relation for $\varphi$ at $\delta$ with respect to $\tau'$ — that is, $J'=\int \varphi(x^{-1}\delta\,\sigma(x))\,w(x)\,s(x)\,d\mu$ for some admissible section function $s$, with $\mu$ the semi-local Haar measure and $w$ the sum of the local weights over the places of $L$ above $v$ — one has $J'=\Phi(a,t)$; and (ii) if $\mathrm{diag}(a,at)$ admits no diagonal norm-string lift $\mathrm{diag}(\alpha,\beta)$ at all, then $\Phi(a,t)=0$. Nothing is asserted about the values $\Phi(a,1)$.
--
--   This packages the twisted weighted orbital integrals of a semi-local test function at diagonal elements into a single function of the torus coordinates $(a,t)$, well defined independently of the chosen lift $\delta$ and of the admissible Haar measure on its twisted centraliser, and locally constant with compact support on the region $t\neq 1$. It is used in the comparison of twisted and untwisted weighted orbital integrals for matching local data in the base-change argument for $\mathrm{GL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_nhds_eq_isCompact_forall_isTwistedWeightedOrbitalIntegral_diagUnits2_eq_of_isSemiLocalTestFn.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_forall_nhds_eq_isCompact_forall_isTwistedWeightedOrbitalIntegral_diagUnits2_eq_of_isSemiLocalTestFn
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    (v : HeightOneSpectrum (𝓞 K))
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ) :
    ∃ Φ : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ,
      (∀ p : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ, p.2 ≠ 1 → ∃ U ∈ nhds p, ∀ q ∈ U, Φ q = Φ p) ∧
      (∃ S : Set ((v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ), IsCompact S ∧
        ∀ a t : (v.adicCompletion K)ˣ, t ≠ 1 → Φ (a, t) ≠ 0 → (a, t) ∈ S) ∧
      ∀ a t : (v.adicCompletion K)ˣ, t ≠ 1 →
        (∀ α β : (L ⊗[K] v.adicCompletion K)ˣ,
            AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
              AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t)) →
          ∀ (τ' : @Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ (diagUnits2 α β))
              (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β))),
            @Measure.IsHaarMeasure _ _ _
              (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ (diagUnits2 α β)) τ' →
            τ' {x | (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) ∈ AutomorphicForm.semiLocalIntegralSet K L v} = 1 →
          ∀ J' : ℂ, AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ (diagUnits2 α β) τ' φ J' →
            J' = Φ (a, t)) ∧
        ((¬ ∃ α β : (L ⊗[K] v.adicCompletion K)ˣ,
            AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
              AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t))) →
          Φ (a, t) = 0) := by sorry
