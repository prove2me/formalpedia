-- Prove2me | Theorems.Thm_Formalism_EigenvalueLevelCeiling_localConditionsFamily_of_weighted
-- name    : Formalism.EigenvalueLevelCeiling.localConditionsFamily_of_weighted
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:43:25.169108+00:00
-- url     : https://prove2.me/theorems/75fac20c-870b-5af5-bba6-9230f5609e8f
-- title:
--   Eigenvalue Level Ceiling: local Conditions Family of weighted
-- statement:
--   The Eigenvalue Level Ceiling construction uses the local Conditions Family of weighted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/GlobalBoundRefinements.lean#L323-L379
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MirabolicMackeyTheory/MirabolicMackeyProofs/GlobalBoundRefinements.lean#L323-L379

import Definitions.Def_Formalism_MirabolicMackeyTheory_LocalConditionsWeighted
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues

theorem Formalism.EigenvalueLevelCeiling.localConditionsFamily_of_weighted (h : LocalConditionsWeighted)
    (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (P : Type) [Group P] [Finite P] (ρ : Representation K P Z)
    (U : Subgroup P) (ψ : P → 𝓞 K) (hMk : IsMackey U ψ)
    (V₀ : Submodule K Z) (e : Z →ₗ[K] Z) (he : e ∘ₗ e = e) (hr : LinearMap.range e = V₀)
    (M Th ThK Th0 ThJ X₃ X₄ : Submodule (𝓞 K) Z)
    (hM : IsLatIn ⊤ M) (hTh : IsLatIn ⊤ Th) (hThK : IsLatIn ⊤ ThK) (hle : Th ≤ M) (hFG : Th0.FG)
    (hEig : Th0 ≤ (eig ρ U ψ).restrictScalars (𝓞 K))
    (hMs : ∀ g : P, M.map ((ρ g).restrictScalars (𝓞 K)) ≤ M)
    (hTs : ∀ g : P, Th.map ((ρ g).restrictScalars (𝓞 K)) ≤ Th)
    (σ : K) (hσ : σ ≠ 0) (hsc : Th ≤ sc σ ThK)
    (hdata : sc ((Nat.card U : ℕ) : K) (cut (eig ρ U ψ) ThK) ≤ Th0)
    (a : K) (E : ℕ) (r : ℝ) (ha : a ≠ 0) (hE : vw w a = (E : ℤ))
    (hT0 : ∀ W : Submodule K Z, (lix w (cut W M) (cut W Th) : ℝ) ≤ (E : ℝ) * (finrank K W : ℝ) + r)
    (h0 : IsLatIn (eig ρ U ψ ⊓ V₀) (Th0.map (e.restrictScalars (𝓞 K))))
    (hJ : IsLatIn (eig ρ U ψ ⊓ V₀) (ThJ.map (e.restrictScalars (𝓞 K)))) (h0J : Th0 ≤ ThJ)
    (h3 : IsLatIn (eig ρ U ψ ⊓ V₀) X₃) (h4 : IsLatIn (eig ρ U ψ ⊓ V₀) X₄) (h34 : X₃ ≤ X₄)
    (ε : ℝ)
    (hTW : (lix w (cut (eig ρ U ψ ⊓ V₀) M) X₃ : ℝ) ≤
      (lix w (cut (eig ρ U ψ ⊓ V₀) M) (ThJ.map (e.restrictScalars (𝓞 K))) : ℝ) + ε)
    (d : ℕ) (φ : (Fin d → K) →ₗ[K] Z) (hinj : Function.Injective φ)
    (hrng : LinearMap.range φ = eig ρ U ψ ⊓ V₀)
    (Mj Tj : Submodule (𝓞 K) (Fin d → K))
    (hMj : Mj.map (φ.restrictScalars (𝓞 K)) = cut (eig ρ U ψ ⊓ V₀) M)
    (hTj : Tj.map (φ.restrictScalars (𝓞 K)) = X₄) :
      (idx w Mj Tj : ℝ) ≤
        ((E : ℝ) - (vw w σ : ℝ) + (vw w ((Nat.card U : ℕ) : K) : ℝ)) * (d : ℝ) +
          (r + (finrank K Z : ℝ) * (vw w ((Nat.card U : ℕ) : K) : ℝ)) / (U.index : ℝ) + ε := by sorry
