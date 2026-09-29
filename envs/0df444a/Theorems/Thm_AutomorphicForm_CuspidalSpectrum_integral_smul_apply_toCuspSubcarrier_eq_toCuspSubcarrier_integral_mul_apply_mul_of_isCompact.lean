-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_apply_mul_of_isCompact
-- name    : AutomorphicForm.CuspidalSpectrum.integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_apply_mul_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/6813d7fb-8706-5271-a4dd-25da1214d582
-- title:
--   Lifted averages over compact finite-adelic subgroups are averages of translates
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta$ be reals and let $\Phi_0$ be a subset of $\mathrm{GL}_2(\mathbb{A}_F)$ which is a slab fundamental domain in the sense of `IsSlabFundamentalDomain`: $0<\alpha<\beta$, every $g\in\Phi_0$ has idèle norm of $\det g$ in $[\alpha,\beta]$, and $\Phi_0$ is a fundamental domain for the action of the image of $\mathrm{GL}_2(F)$ on $\mathrm{GL}_2(\mathbb{A}_F)$ for the adelic Haar measure restricted to that determinant slab. Let $\sigma$ be a real parameter and $\xi$ a homomorphism from the full subgroup of $(\mathbb{A}_F)^\times$ to $\mathbb{C}^\times$. Let $U$ be a subgroup of $\mathrm{GL}_2(\mathbb{A}_F)$ whose underlying set is compact and which is contained in `finiteAdelicGL2Subgroup F`, the kernel of the archimedean-component map, and equip $U$ with a Borel measurable structure and a finite measure $\mu$. Let $S$ assign to each $u\in U$ a continuous $\mathbb{C}$-linear endomorphism of the cuspidal subcarrier $\mathrm{cuspSubcarrier}\,F\,h_{\Phi_0}\,\sigma\,\xi$ — the topological closure, inside the carrier $\mathrm{Carrier}\,F\,\Phi_0\,\sigma$, of the image under `toCarrier` of the submodule `cuspMemberSubmodule F Φ₀ ξ` of functions satisfying the predicate `IsSmoothCuspAutomorphicFnAt` for the pin data `fdPins F Φ₀` and $\xi$ and which are continuous. Assume each $S\,u$ lifts right translation by $u$ in the sense of `IsCuspLift`: for every cuspidal member $\varphi$ and every witness that $x\mapsto\varphi(xu)$ is again such a member, $S\,u$ carries the class of $\varphi$ to the class of $x\mapsto\varphi(xu)$; assume also that $u\mapsto S\,u\,v$ is continuous for each $v$. Finally let $c:U\to\mathbb{C}$ be continuous and $\varphi$ a cuspidal continuous member. Then the function $x\mapsto\int_U c(u)\,\varphi(xu)\,d\mu(u)$ again belongs to `cuspMemberSubmodule F Φ₀ ξ`, and (for that membership witness) the vector-valued integral $\int_U c(u)\cdot S\,u\,[\varphi]\,d\mu(u)$ in the cuspidal subcarrier equals the class of that averaged function.
--
--   This is the integrated-representation compatibility statement for the cuspidal subcarrier over a compact group of finite adelic matrices: averaging the lifted operators against a continuous weight agrees with averaging the automorphic function itself over right translates. It is used to produce averaging operators at finite level, being cited by [`AutomorphicForm.CuspidalSpectrum.exists_idempotent_levelAverage_of_isCompact`](thm.html#AutomorphicForm.CuspidalSpectrum.exists_idempotent_levelAverage_of_isCompact).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_apply_mul_of_isCompact.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.CuspidalSpectrum.integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_apply_mul_of_isCompact
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (hUf : U ≤ finiteAdelicGL2Subgroup F)
    [MeasurableSpace ↥U] [BorelSpace ↥U] (μ : Measure ↥U) [IsFiniteMeasure μ]
    (S : ↥U → (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)))
    (hS : ∀ u : ↥U, IsCuspLift F hΦ₀ σ ξ (rightTranslate F (u : AdelicGL2 (𝓞 F) F)) (S u))
    (hSc : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), Continuous fun u : ↥U => S u v)
    (c : ↥U → ℂ) (hc : Continuous c)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ) :
    ∃ h : (fun x => ∫ u, c u * φ (x * (u : AdelicGL2 (𝓞 F) F)) ∂μ) ∈ cuspMemberSubmodule F Φ₀ ξ,
      ∫ u, c u • S u (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) ∂μ =
        toCuspSubcarrier F hΦ₀ σ ξ ⟨fun x => ∫ u, c u * φ (x * (u : AdelicGL2 (𝓞 F) F)) ∂μ, h⟩ := by sorry
