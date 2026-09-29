-- Prove2me | Theorems.Thm_AutomorphicForm_eq_zero_of_isInducedSection_of_isArchKFinite_of_forall_mem_span_range_of_principalLevel_bot
-- name    : AutomorphicForm.eq_zero_of_isInducedSection_of_isArchKFinite_of_forall_mem_span_range_of_principalLevel_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/05f8ddf7-24d9-5ff3-9857-7780dab2dd8c
-- title:
--   Finitely spanned K-finite induced sections at trivial level vanish
-- statement:
--   Let $F$ be a number field, with adele ring $\mathbb{A} =$ `AdeleRing (𝓞 F) F` carried with its Borel measurable structure, and let `tysF` be a family of archimedean types, i.e. a cardinality $\mathrm{card}(w) \in \mathbb{N}$ together with representations $\mathrm{rep}(w,i) \in$ `ArchRepAt F w` for $i < \mathrm{card}(w)$, indexed by the infinite places $w$ of $F$. Write $\alpha_m \colon \mathbb{A}^\times \to \mathbb{R}^\times$ for the character of units obtained from the distributive Haar character of $\mathbb{A}$ by composing with $\mathbb{R}_{\ge 0} \to \mathbb{R}$, and assume $\alpha_m(x) > 0$ for all $x$. Let $\mu, \nu \colon \mathbb{A}^\times \to \mathbb{C}^\times$ be continuous characters with $\|\mu(x)\| = \|\nu(x)\| = 1$ for all $x$, let $t \in \mathbb{R}$, let $n \in \mathbb{N}$ and let $\psi \colon \mathrm{Fin}\, n \to (\mathrm{GL}_2(\mathbb{A}) \to \mathbb{C})$ be a finite family of functions. Put $s = it$, $\eta_1 = \mu \cdot \alpha_m^{\,s+1/2}$ and $\eta_2 = \nu \cdot \alpha_m^{-(s+1/2)}$ (complex powers of the positive real $\alpha_m$), and call $\varphi_0 \colon \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ an induced section if $\varphi_0(bg) = \eta_1(b_{00})\,\eta_2(b_{11})\,\varphi_0(g)$ for all $g$ and all $b$ in the adelic Borel subgroup (lower left entry zero). Assume that every induced section $\varphi_0$ which is continuous, archimedean $K$-finite (for each infinite place $w$ the right translates of $\varphi_0$ by `archRowIsometrySubgroup F w` span a finite-dimensional space), invariant under right multiplication by every element of `principalLevel (𝓞 F) F ⊥ ⊓ finiteAdelicGL2Subgroup F` (the principal level subgroup at the zero ideal, intersected with the kernel of the archimedean projection `glArch`), and lying in `archCutSubmodule F tysF` — the infimum over infinite places $w$ of the supremum over $i < \mathrm{card}(w)$ of the type submodules `archTypeSubmoduleAt F w (tysF.rep w i)` — belongs to the $\mathbb{C}$-span of the range of $\psi$. Then every continuous, archimedean $K$-finite induced section $\varphi_0$ lying in `archCutSubmodule F tysF` is identically zero, with no invariance hypothesis imposed.
--
--   This is the statement that the space of continuous, archimedean $K$-finite sections of the principal series $I(\mu\|\cdot\|^{it+1/2}, \nu\|\cdot\|^{-(it+1/2)})$ of $\mathrm{GL}_2(\mathbb{A})$ with prescribed archimedean types admits no finite spanning family unless it is zero, the level imposed being that of the zero ideal, so that no congruence condition at the finite places is in force. It is used in the analytic estimates for Maass–Selberg pairings along vertical lines that feed the global integral computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_zero_of_isInducedSection_of_isArchKFinite_of_forall_mem_span_range_of_principalLevel_bot.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open IsDedekindDomain
open scoped NNReal

theorem AutomorphicForm.eq_zero_of_isInducedSection_of_isArchKFinite_of_forall_mem_span_range_of_principalLevel_bot
    (F : Type) [Field F] [NumberField F] (tysF : ArchTypeFamily F) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 F) F)ˣ => ((ν z : ℂˣ) : ℂ))
      (t : ℝ) (n : ℕ) (ψ : Fin n → AdelicGL2 (𝓞 F) F → ℂ),
      (∀ φ₀ : AdelicGL2 (𝓞 F) F → ℂ,
        IsInducedSection (𝓞 F) F (etaFst μ αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite F φ₀ →
        (∀ (g : AdelicGL2 (𝓞 F) F), ∀ u ∈ principalLevel (𝓞 F) F ⊥ ⊓ finiteAdelicGL2Subgroup F, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule F tysF →
        φ₀ ∈ Submodule.span ℂ (Set.range ψ)) →
    ∀ (φ₀ : AdelicGL2 (𝓞 F) F → ℂ),
      IsInducedSection (𝓞 F) F (etaFst μ αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν αm hαm ((t : ℂ) * Complex.I)) φ₀ →
      Continuous φ₀ → IsArchKFinite F φ₀ → φ₀ ∈ archCutSubmodule F tysF → φ₀ = 0 := by sorry
