-- Prove2me | Theorems.Thm_AutomorphicForm_exists_entire_whittakerCoefficient_bruhatEisenstein_eq_eulerProduct_mul_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family_of_unitary
-- name    : AutomorphicForm.exists_entire_whittakerCoefficient_bruhatEisenstein_eq_eulerProduct_mul_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family_of_unitary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/06173e00-db76-5047-9070-721cc4839bb9
-- title:
--   Entire Whittaker coefficients of the GL₂ Bruhat Eisenstein family
-- statement:
--   Let $F$ be a number field, and let $\alpha$ be the real-valued character of the idele group obtained from the distributive Haar character of $\mathbb{A}_F$ (taken into $\mathbb{R}^\times$), assumed pointwise positive. Let $\mu,\nu$ be characters of $\mathbb{A}_F^\times$ into $\mathbb{C}^\times$ that are unitary ($|\chi(x)|=1$ for all $x$) and trivial on the principal ideles $F^\times$, let $\psi$ be an additive character of $\mathbb{A}_F$ that is trivial on $F$, continuous and nontrivial, and let $\varphi$ be a family $s\mapsto\varphi_s$ on $\mathrm{GL}_2(\mathbb{A}_F)$ such that each $\varphi_s$ satisfies the induction rule $\varphi_s(bg)=\eta_1(b_{00})\eta_2(b_{11})\varphi_s(g)$ for $b$ in the adelic Borel subgroup (matrices with vanishing lower-left entry), where $\eta_1=\mu\cdot\alpha^{s+1/2}$ and $\eta_2=\nu\cdot\alpha^{-(s+1/2)}$; each $\varphi_s$ is $K_\infty$-finite (its right translates under the row-isometry subgroup at each infinite place span a finite-dimensional space) and $K_f$-smooth (its stabiliser in the finite-adelic subgroup, the kernel of the archimedean projection, is open); $\varphi$ is jointly continuous and entire in $s$ for each fixed group element. Let $\varpi=(\varpi_v)_v$ be local uniformisers, $\mathrm{v}(\varpi_v)=\mathrm{ofAdd}(-1)$. Put $E_s(h)=\varphi_s(h)+\sum_{\xi\in F}\varphi_s(w\,n(\xi)h)$, with $w$ the image of $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $n(\xi)$ the upper unipotent, and $\mathrm{hgt}(b)=\alpha(b_{00})/\alpha(b_{11})$. The assertion is the existence of a finite set $S$ of finite places and of functions $\mathcal{V}_\xi(s,h)$, indexed by $\xi\in F$ with $\xi\neq0$, such that: $s\mapsto\mathcal{V}_\xi(s,h)$ is entire for every $h$; for $\mathrm{Re}\,s>1$ the Whittaker coefficient of $E_s$ at $\xi$ and $h$, the integral $\int \varphi(n(x)h)\psi(-\xi x)$ taken against the measure fixed by `productionPins F` (the adelic additive Haar measure conditioned on the adelic box), equals $\prod_{v\notin S}\bigl(1-(\mu\nu^{-1})_v(\varpi_v)\,N(v)^{-(2s+1)}\bigr)\cdot\mathcal{V}_\xi(s,h)$, where $(\mu\nu^{-1})_v$ denotes $\mu\nu^{-1}$ restricted to the local units at $v$; each $\mathcal{V}_\xi$ is jointly continuous in $(s,h)$; for all compact $C\subseteq\mathbb{C}$ and compact $\Omega\subseteq\mathrm{GL}_2(\mathbb{A}_F)$ there is a summable $u$ with $\|\mathcal{V}_\xi(s,h)\|\le u_\xi$ for $s\in C$, $h\in\Omega$; and for all such $C,\Omega$, all $c'>0$ and all $N\in\mathbb{N}$ there is $M$ with $\xi\mapsto\|\mathcal{V}_\xi(s,b\omega)\|$ summable and $\sum_{\xi\neq0}\|\mathcal{V}_\xi(s,b\omega)\|\le M\,\mathrm{hgt}(b)^{-N}$ whenever $s\in C$, $\omega\in\Omega$, $b$ lies in the adelic Borel subgroup and $\mathrm{hgt}(b)\ge c'$.
--
--   This is the Fourier–Whittaker expansion of the Bruhat-type Eisenstein family attached to two unitary idele class characters, with the partial Euler block $L^S(2s+1,\mu\nu^{-1})^{-1}$ divided out so that the individual coefficients are entire on the whole $s$-plane and decay faster than any power of the height on Siegel-type regions. It feeds the comparison of the Eisenstein family with its constant term in [`AutomorphicForm.exists_entire_eq_mul_bruhatEisenstein_sub_constantTerm_norm_le_rpow_neg_of_isArchKFinite_family_of_unitary`](thm.html#AutomorphicForm.exists_entire_eq_mul_bruhatEisenstein_sub_constantTerm_norm_le_rpow_neg_of_isArchKFinite_family_of_unitary).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_entire_whittakerCoefficient_bruhatEisenstein_eq_eulerProduct_mul_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family_of_unitary.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPins
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.InfinitePlace
open AutomorphicForm
open AutomorphicForm.WindowedSiegel Filter Topology IsDedekindDomain
open scoped NNReal

open scoped Classical in

theorem AutomorphicForm.exists_entire_whittakerCoefficient_bruhatEisenstein_eq_eulerProduct_mul_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family_of_unitary
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμF : IsIdeleClassChar (𝓞 F) F μ) (_hνF : IsIdeleClassChar (𝓞 F) F ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (_hψ : IsGlobalAddChar F ψ)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
      (_hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)),
    let E : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s h =>
      φ s h + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * h)
    let hgt : ↥(adelicBorel (𝓞 F) F) → ℝ := fun b =>
      ((α (borelDiagFst b) : ℝˣ) : ℝ) / ((α (borelDiagSnd b) : ℝˣ) : ℝ)
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (𝒱 : {ξ : F // ξ ≠ 0} → ℂ → AdelicGL2 (𝓞 F) F → ℂ),
      (∀ (ξ : {ξ : F // ξ ≠ 0}) (h : AdelicGL2 (𝓞 F) F), Differentiable ℂ (fun s => 𝒱 ξ s h)) ∧
      (∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ) (h : AdelicGL2 (𝓞 F) F), 1 < s.re →
        whittakerCoefficient F (productionPins F) ψ (E s) (ξ : F) h
          = (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
              (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) * 𝒱 ξ s h) ∧
      (∀ ξ : {ξ : F // ξ ≠ 0}, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => 𝒱 ξ p.1 p.2)) ∧
      (∀ (C : Set ℂ) (Ω : Set (AdelicGL2 (𝓞 F) F)), IsCompact C → IsCompact Ω →
        ∃ u : {ξ : F // ξ ≠ 0} → ℝ, Summable u ∧
          ∀ (ξ : {ξ : F // ξ ≠ 0}), ∀ s ∈ C, ∀ h ∈ Ω, ‖𝒱 ξ s h‖ ≤ u ξ) ∧
      (∀ (C : Set ℂ) (Ω : Set (AdelicGL2 (𝓞 F) F)) (c' : ℝ) (N : ℕ),
        IsCompact C → IsCompact Ω → 0 < c' →
        ∃ M : ℝ, ∀ s ∈ C, ∀ (b : ↥(adelicBorel (𝓞 F) F)) (ω : AdelicGL2 (𝓞 F) F),
          ω ∈ Ω → c' ≤ hgt b →
            Summable (fun ξ : {ξ : F // ξ ≠ 0} => ‖𝒱 ξ s ((b : AdelicGL2 (𝓞 F) F) * ω)‖) ∧
            ∑' ξ : {ξ : F // ξ ≠ 0}, ‖𝒱 ξ s ((b : AdelicGL2 (𝓞 F) F) * ω)‖ ≤ M * (hgt b) ^ (-(N : ℝ))) := by sorry
