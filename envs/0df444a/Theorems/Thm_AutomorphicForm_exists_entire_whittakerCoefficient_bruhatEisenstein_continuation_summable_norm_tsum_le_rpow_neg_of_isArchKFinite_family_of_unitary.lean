-- Prove2me | Theorems.Thm_AutomorphicForm_exists_entire_whittakerCoefficient_bruhatEisenstein_continuation_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family_of_unitary
-- name    : AutomorphicForm.exists_entire_whittakerCoefficient_bruhatEisenstein_continuation_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family_of_unitary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/11da054a-54a3-5fba-af25-0f47336f306b
-- title:
--   Entire L-normalised Whittaker terms of the Bruhat–Eisenstein family
-- statement:
--   Let $F$ be a number field and let $\alpha$ be the homomorphism from the ideles of $F$ to $\mathbb{R}^{\times}$ obtained from the distributive Haar character of the adele ring, assumed pointwise positive. Let $\mu,\nu$ be characters of the ideles with values in $\mathbb{C}^{\times}$ that are unitary ($\|\chi(x)\|=1$ for all $x$) and trivial on the principal ideles, let $\psi$ be an additive character of $\mathbb{A}_F$ that is trivial on $F$, continuous and nontrivial, and let $\varphi:\mathbb{C}\to \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a family such that each $\varphi_s$ transforms under the adelic Borel subgroup (lower-left entry zero) by $b\mapsto \mu\alpha^{s+1/2}(b_{00})\,\nu\alpha^{-(s+1/2)}(b_{11})$, is $K_\infty$-finite at every infinite place (its right translates under the row-isometry subgroup span a finite-dimensional space) and $K_f$-smooth (its stabiliser in the finite part of $\mathrm{GL}_2$ is open), with $(s,g)\mapsto\varphi_s(g)$ continuous and $s\mapsto\varphi_s(g)$ entire. Put $E_s(h)=\varphi_s(h)+\sum'_{\xi\in F}\varphi_s(w\,n(\xi)h)$, where $w$ is the image of $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $n(x)$ is the upper unipotent, and $\mathrm{hgt}(b)=\alpha(b_{00})/\alpha(b_{11})$ for $b$ in the adelic Borel subgroup. Then there is a finite set $S_0$ of finite places such that for every finite $S\supseteq S_0$ and every choice of local units $\varpi_v$ of valuation $-1$ there exists $\mathcal{W}:\{\xi\in F:\xi\neq0\}\to\mathbb{C}\to\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ with: (i) $s\mapsto\mathcal{W}_\xi(s,h)$ entire for all $\xi,h$; (ii) for $\operatorname{Re}s>1$, $\mathcal{W}_\xi(s,h)$ equals the product over $v\notin S$ of $(1-(\mu\nu^{-1})_v(\varpi_v)\,N(v)^{-(2s+1)})^{-1}$ times the $\xi$-th Whittaker coefficient of $E_s$ at $h$, formed with $\psi$ and the fixed integration data `productionPins F`; (iii) each $(s,h)\mapsto\mathcal{W}_\xi(s,h)$ continuous; (iv) for compact $C\subseteq\mathbb{C}$ and compact $\Omega$ a summable majorant $u$ with $\|\mathcal{W}_\xi(s,h)\|\le u_\xi$ for $s\in C$, $h\in\Omega$; (v) for compact $C,\Omega$, $c'>0$ and $N\in\mathbb{N}$ a constant $M$ with $\sum_{\xi\neq0}\|\mathcal{W}_\xi(s,b\omega)\|$ summable and $\le M\,\mathrm{hgt}(b)^{-N}$ whenever $s\in C$, $\omega\in\Omega$ and $\mathrm{hgt}(b)\ge c'$.
--
--   This is the whole-plane form of the analytic theory of the Fourier–Whittaker expansion of the $\mathrm{GL}_2$ Eisenstein series attached to a pair of unitary idele class characters: after multiplication by the partial Hecke $L$-factor $L^S(2s+1,\mu\nu^{-1})$ the individual Whittaker terms become entire in $s$, jointly continuous, dominated by a summable majorant on compacta, and rapidly decaying in the Borel height. It feeds the analytic continuation of the Bruhat–Eisenstein series minus its constant term to $\operatorname{Re}s\ge0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_entire_whittakerCoefficient_bruhatEisenstein_continuation_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family_of_unitary.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPins
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.exists_entire_whittakerCoefficient_bruhatEisenstein_continuation_summable_norm_tsum_le_rpow_neg_of_isArchKFinite_family_of_unitary
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
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g)),
    let E : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s h =>
      φ s h + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * h)
    let hgt : ↥(adelicBorel (𝓞 F) F) → ℝ := fun b =>
      ((α (borelDiagFst b) : ℝˣ) : ℝ) / ((α (borelDiagSnd b) : ℝˣ) : ℝ)
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)),
      ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), S₀ ⊆ S →
      ∀ (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ),
        (∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) →
      ∃ 𝒲 : {ξ : F // ξ ≠ 0} → ℂ → AdelicGL2 (𝓞 F) F → ℂ,
        (∀ (ξ : {ξ : F // ξ ≠ 0}) (h : AdelicGL2 (𝓞 F) F),
          Differentiable ℂ (fun s => 𝒲 ξ s h)) ∧
        (∀ (ξ : {ξ : F // ξ ≠ 0}) (s : ℂ) (h : AdelicGL2 (𝓞 F) F), 1 < s.re →
          𝒲 ξ s h
            = (∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S},
                (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                  * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))⁻¹)
              * whittakerCoefficient F (productionPins F) ψ (E s) (ξ : F) h) ∧
        (∀ ξ : {ξ : F // ξ ≠ 0}, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => 𝒲 ξ p.1 p.2)) ∧
        (∀ (C : Set ℂ) (Ω : Set (AdelicGL2 (𝓞 F) F)), IsCompact C → IsCompact Ω →
          ∃ u : {ξ : F // ξ ≠ 0} → ℝ, Summable u ∧
            ∀ (ξ : {ξ : F // ξ ≠ 0}), ∀ s ∈ C, ∀ h ∈ Ω, ‖𝒲 ξ s h‖ ≤ u ξ) ∧
        (∀ (C : Set ℂ) (Ω : Set (AdelicGL2 (𝓞 F) F)) (c' : ℝ) (N : ℕ),
          IsCompact C → IsCompact Ω → 0 < c' →
          ∃ M : ℝ, ∀ s ∈ C, ∀ (b : ↥(adelicBorel (𝓞 F) F)) (ω : AdelicGL2 (𝓞 F) F),
            ω ∈ Ω → c' ≤ hgt b →
              Summable (fun ξ : {ξ : F // ξ ≠ 0} => ‖𝒲 ξ s ((b : AdelicGL2 (𝓞 F) F) * ω)‖) ∧
              ∑' ξ : {ξ : F // ξ ≠ 0}, ‖𝒲 ξ s ((b : AdelicGL2 (𝓞 F) F) * ω)‖
                ≤ M * (hgt b) ^ (-(N : ℝ))) := by sorry
