-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_mem_inf_norm_toCuspSubcarrier_sub_lt_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt
-- name    : AutomorphicForm.CuspidalSpectrum.exists_mem_inf_norm_toCuspSubcarrier_sub_lt_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/c07aded6-377c-5f64-9cb3-2ca0857c8d1a
-- title:
--   Carrier-norm approximation inside a cuspidal subrepresentation from ample-window L² closeness
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2,\kappa$ be real with $d_1<d_2$, $1\le\kappa$, $0<c$, $0<d_1$, and let $T$ be a finite subset of $\mathrm{GL}_2$ of the adeles of $F$. Write $W=\bigcup_{x\in T}(\cdot\,x)''\,$ of the ample centre-cut Siegel set $\mathrm{centreCutSiegelSetAmple}\,F\,c\,u\,d_1\,d_2\,\kappa$ (finite part integral, all local heights $\ge c$, all $x$-windows $\le u^2$, all archimedean determinant norms in $[d_1,d_2]$, and local heights mutually comparable within the factor $\kappa$), and $W_0$ for the corresponding union built from the plain centre-cut Siegel set. Assume $W$ covers $\mathrm{GL}_2$ of the adeles modulo global points and central ideles. Let $\xi$ be a homomorphism from all idele units to $\mathbb{C}^\times$ with $\|\xi(z)\|=\|z\|^{\sigma}$ for the idele norm, let $\Phi_0$ be a slab fundamental domain with parameters $\alpha<\beta$, let $N\neq 0$ be an ideal of the ring of integers, and let $\mathrm{tys}$ be an archimedean type family. Let $V$ be a $\mathbb{C}$-submodule of functions which is a cuspidal subrepresentation (`IsCuspSubrep`) for the pins `productionPinsOf` with domain $W_0$, level subgroups $\mathrm{levelOne}(N)\sqcap$ the finite-adelic subgroup, Hecke generators, and the adelic box, and let $\varphi_1\in V$. Let $\varphi$ be continuous, smooth cuspidal automorphic for the same pins with domain $W$, invariant under the level-$N$ subgroup, of type $\mathrm{tys}$, and suppose that for every $\varepsilon>0$ in $[0,\infty]$ there are a finite set $s$ and coefficients $l$ with $\int_W\|\varphi(y)-\sum_{h\in s}l(h)\varphi_1(yh)\|^2<\varepsilon$ for adelic Haar measure. Then for every $\delta>0$: $\varphi$ lies in $\mathrm{cuspMemberSubmodule}\,F\,\Phi_0\,\xi$, and there is an $x$ lying in $V$, level-$N$-invariant, of type $\mathrm{tys}$, also in $\mathrm{cuspMemberSubmodule}\,F\,\Phi_0\,\xi$, whose class under `toCuspSubcarrier` differs from that of $\varphi$ by less than $\delta$ in the cuspidal subcarrier norm.
--
--   This is the analytic step transporting mean-square closeness on the ample covering window to closeness in the weighted $L^2$ carrier attached to a slab fundamental domain, producing a nearby vector that simultaneously lies in the given cuspidal subrepresentation, is invariant under the level-$N$ subgroup and is of the prescribed archimedean type. It feeds the identification of cuspidal constituents, being cited in the proof that a function approximable by translates of a vector of a cuspidal subrepresentation belongs to that representation's typed level-$N$ part.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_mem_inf_norm_toCuspSubcarrier_sub_lt_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.CuspidalSpectrum.exists_mem_inf_norm_toCuspSubcarrier_sub_lt_of_mem_of_forall_exists_setLIntegral_ample_sub_sum_mul_translate_sq_lt
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ κ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hκ : 1 ≤ κ) (hc : 0 < c) (hd₁ : 0 < d₁)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspSubrep F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V)
    (φ₁ : AdelicGL2 (𝓞 F) F → ℂ) (hφ₁ : φ₁ ∈ V)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsSmoothCuspAutomorphicFnAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ)
    (hφc : Continuous φ)
    (hφN : φ ∈ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N)
    (hφt : φ ∈ archCutSubmodule F tys)
    (happrox : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (s : Finset (AdelicGL2 (𝓞 F) F)) (l : AdelicGL2 (𝓞 F) F → ℂ),
        ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ,
            (‖φ y - ∑ h ∈ s, l h * φ₁ (y * h)‖₊ : ℝ≥0∞) ^ 2
              ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ε)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ hφm : φ ∈ cuspMemberSubmodule F Φ₀ ξ,
    ∃ x ∈ V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F tys,
    ∃ hxm : x ∈ cuspMemberSubmodule F Φ₀ ξ,
      ‖toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨x, hxm⟩‖ < δ := by sorry
