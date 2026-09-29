-- Prove2me | Theorems.Thm_AutomorphicForm_exists_norm_eulerProduct_mul_intertwining_le_mul_one_add_norm_eulerProduct_of_isInducedSection
-- name    : AutomorphicForm.exists_norm_eulerProduct_mul_intertwining_le_mul_one_add_norm_eulerProduct_of_isInducedSection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/104e18a0-e1b0-5feb-8f84-1c48c127d4be
-- title:
--   Strip bound for intertwining operator times Hecke Euler product
-- statement:
--   Let $F$ be a number field, let $\alpha$ be the character of the idele group $(\mathbb{A}_F)^\times$ obtained from the distributive Haar character of the adele ring by passing through $\mathbb{R}_{\ge 0}\to\mathbb{R}$ and taking values in units, and assume $\alpha(x)>0$ for all $x$. Let $\mu,\nu:(\mathbb{A}_F)^\times\to\mathbb{C}^\times$ be characters that are unitary ($|\chi(x)|=1$ for all $x$), trivial on the principal ideles coming from $F^\times$, and continuous. Let $\varphi:\mathbb{C}\times \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be such that for each $s$ the function $\varphi_s$ satisfies $\varphi_s(bg)=\eta_1(b)\eta_2(b)\varphi_s(g)$ for $b$ in the adelic Borel subgroup, with $\eta_1=\mu\,\alpha^{s+1/2}$ and $\eta_2=\nu\,\alpha^{-(s+1/2)}$ evaluated on the two diagonal entries of $b$; each $\varphi_s$ is $K$-finite at every archimedean place and a smooth vector for right translation by the finite adelic $\mathrm{GL}_2$; $\varphi$ is jointly continuous and holomorphic in $s$ for each $g$; and for every infinite place $w$ there is a finite-dimensional subspace $W$ of functions on the row-isometry subgroup at $w$ containing all functions $k\mapsto\varphi_s(gk)$. Let $Mc:\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be such that for each $g$ the function $s\mapsto Mc(s,g)$ is meromorphic in normal form on all of $\mathbb{C}$ and equals the Weyl intertwining integral $\int \varphi_s(w^{-1}n(x)g)\,dx$ against adelic additive Haar measure for $\mathrm{Re}\,s>1/2$, and let $\sigma_0>0$. Write $E(w)$ for the Euler product over all finite places $v$ of $(1-c_v N(v)^{-w})^{-1}$, where $c_v=(\mu\nu^{-1})(\varpi_v)$ at a uniformiser idele if $\mu\nu^{-1}$ is unramified at $v$ and $c_v=0$ otherwise. Then two assertions hold. First, for every real $\tau$ with $\mu\nu^{-1}=|\cdot|^{i\tau}$ and every entire $Q$ with $Q(w)=(w-(1-i\tau))E(w)$ for $\mathrm{Re}\,w>1$, there exist $A\ge 0$ and $N\in\mathbb{N}$ with $\|(s-(1/2-i\tau/2))Q(2s+1)Mc(s,k)\|\le A(1+|\mathrm{Im}\,s|)^N(1+\|Q(2s)\|)\sup_{k'\in K}\|\varphi_s(k')\|$ for all $s$ with $0\le\mathrm{Re}\,s\le\sigma_0$ and all $k$ in the maximal compact subgroup $K$ (finite part integral, archimedean components row isometries). Second, if $\mu\nu^{-1}\ne|\cdot|^{i\tau}$ for every real $\tau$, then for every entire $L$ with $L(w)=E(w)$ for $\mathrm{Re}\,w>1$ there exist $A\ge 0$ and $N$ with $\|L(2s+1)Mc(s,k)\|\le A(1+|\mathrm{Im}\,s|)^N(1+\|L(2s)\|)\sup_{k'\in K}\|\varphi_s(k')\|$ on the same range.
--
--   This is the vertical growth estimate, uniform on the closed strip $0\le\mathrm{Re}\,s\le\sigma_0$, for the meromorphically continued Weyl intertwining operator of $\mathrm{GL}_2$ multiplied by the Hecke Euler product of $\mu\nu^{-1}$ at $2s+1$, with the growth measured against the size of that Euler product at $2s$ and the sup-norm of the inducing section on the maximal compact subgroup. It feeds the polynomial-bound statement for the continued Euler-product-times-intertwining function used in the analytic input to the Eisenstein theory.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_norm_eulerProduct_mul_intertwining_le_mul_one_add_norm_eulerProduct_of_isInducedSection.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_HeckeEigenfunction
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.Analysis.Meromorphic.NormalForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm
open scoped NNReal
open scoped Classical in

theorem
    AutomorphicForm.exists_norm_eulerProduct_mul_intertwining_le_mul_one_add_norm_eulerProduct_of_isInducedSection
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (_hφKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (Mc : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hMc : ∀ g : AdelicGL2 (𝓞 F) F,
        (letI := adeleBorel (𝓞 F) F
         MeromorphicNFOn (fun s : ℂ => Mc s g) Set.univ ∧
          ∀ s : ℂ, (1 / 2 : ℝ) < s.re →
            Mc s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ s) g))
      (σ₀ : ℝ) (_hσ₀ : 0 < σ₀),
    (∀ τ : ℝ, μ * ν⁻¹ = NumberField.TateGlobal.normPowChar F τ →
      ∀ Q : ℂ → ℂ, Differentiable ℂ Q →
        (∀ w : ℂ, 1 < w.re → Q w = (w - ((1 : ℂ) - ((τ : ℝ) : ℂ) * Complex.I)) *
          ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) //
              v ∉ (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))},
            (1 - (if NumberField.TateGlobal.IsUnramifiedCharAt (μ * ν⁻¹) v.1 then
                    (((μ * ν⁻¹) (AutomorphicForm.uniformizerIdele F v.1) : ℂˣ) : ℂ) else 0) *
                  (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹) →
        ∃ A : ℝ, 0 ≤ A ∧ ∃ N : ℕ, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ σ₀ →
          ∀ k : AdelicGL2 (𝓞 F) F, k ∈ adelicMaximalCompact F →
            ‖(s - ((1 / 2 : ℂ) - ((τ / 2 : ℝ) : ℂ) * Complex.I)) * Q (2 * s + 1) * Mc s k‖ ≤
              A * (1 + |s.im|) ^ N * (1 + ‖Q (2 * s)‖) *
                ⨆ k' : ↥(adelicMaximalCompact F), ‖φ s (k' : AdelicGL2 (𝓞 F) F)‖) ∧
    ((∀ τ : ℝ, μ * ν⁻¹ ≠ NumberField.TateGlobal.normPowChar F τ) →
      ∀ L : ℂ → ℂ, Differentiable ℂ L →
        (∀ w : ℂ, 1 < w.re → L w =
          ∏' v : {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) //
              v ∉ (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))},
            (1 - (if NumberField.TateGlobal.IsUnramifiedCharAt (μ * ν⁻¹) v.1 then
                    (((μ * ν⁻¹) (AutomorphicForm.uniformizerIdele F v.1) : ℂˣ) : ℂ) else 0) *
                  (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-w)))⁻¹) →
        ∃ A : ℝ, 0 ≤ A ∧ ∃ N : ℕ, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ σ₀ →
          ∀ k : AdelicGL2 (𝓞 F) F, k ∈ adelicMaximalCompact F →
            ‖L (2 * s + 1) * Mc s k‖ ≤
              A * (1 + |s.im|) ^ N * (1 + ‖L (2 * s)‖) *
                ⨆ k' : ↥(adelicMaximalCompact F), ‖φ s (k' : AdelicGL2 (𝓞 F) F)‖) := by sorry
