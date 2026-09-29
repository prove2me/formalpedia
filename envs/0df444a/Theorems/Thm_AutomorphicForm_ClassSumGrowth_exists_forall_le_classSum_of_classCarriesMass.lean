-- Prove2me | Theorems.Thm_AutomorphicForm_ClassSumGrowth_exists_forall_le_classSum_of_classCarriesMass
-- name    : AutomorphicForm.ClassSumGrowth.exists_forall_le_classSum_of_classCarriesMass
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/cfa3a069-9a0d-5c22-a13f-0bb492081751
-- title:
--   Linear lower bound for class-restricted mean-square Hecke sums
-- statement:
--   Let $K$ be a number field and $\alpha,\beta$ real numbers with $0<\beta$ and $\alpha<\beta$. Let $\Phi_0\subseteq \mathrm{GL}_2(\mathbb{A}_K)$ be a fundamental domain for the image of $\mathrm{GL}_2(K)$ under `globalPoints` with respect to the adelic Haar measure `adelicGLHaar` restricted to $\{g : \|\det g\|_{\mathbb{A}} \in [\alpha,\beta]\}$, the idele norm being [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19). Fix the carrier data `productionPinsOf K Φ₀ …`, whose level subgroups are $\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, whose Hecke elements are `heckeGen`, whose adelic box is `adelicBox K`, and whose central subgroup $Z$ is all of $(\mathbb{A}_K)^\times$; let $\xi : Z \to \mathbb{C}^\times$ be a character with $\|\xi(z)\| = \|z\|_{\mathbb{A}}^{\sigma}$ for all ideles $z$, for some $\sigma\in\mathbb{R}$. Let $N\neq 0$ be an ideal of $\mathcal{O}_K$, let $S$ be a finite set of finite places containing every $v$ dividing $N$ and every $v$ dividing the different $\mathfrak{d}_{\mathcal{O}_K/\mathbb{Z}}$, and let $\Psi$ be a complex Hecke eigensystem (a level, nonzero, together with eigenvalue families $a,b$) such that the isotypic cuspidal submodule `isotypicCuspSubmodule K … ξ N S Ψ` — the $\mathbb{C}$-span of the functions satisfying `IsIsotypicCuspFormAt` for these data — contains a nonzero element. For a nonzero ideal $\mathfrak{n}$ with no $v\in S$ dividing it, write $c(\mathfrak{n}) = \prod_{v}^{\mathrm{f}} C_v(\mathrm{ord}_v\mathfrak{n})$, where $C_v$ is the sequence `heckeRecursionSeq` with parameters $\mathrm{N}v = |\mathcal{O}_K/v|$, $\lambda = \Psi.a(v)$ and $\omega = (\mathrm{N}v)^{-1}\Psi.b(v)$, i.e. $C_v(0)=1$, $C_v(1)=\lambda/\mathrm{N}v$ and $C_v(m+2) = (\lambda C_v(m+1)-\omega C_v(m))/\mathrm{N}v$, and the exponent is the multiplicity of $v$ in $\mathfrak{n}$ read as a natural number. Then there exist $c_L>0$ and $Y_0\ge 1$ such that for every ideal class $\mathcal{C}$ of $\mathcal{O}_K$ that contains some such $\mathfrak{n}$ with $c(\mathfrak{n})\neq 0$, and every $Y\ge Y_0$, one has the inequality in $[0,\infty]$ $$c_L\,Y \le \sum_{\mathfrak{n}} \|c(\mathfrak{n})\|^2\,(\mathrm{N}\mathfrak{n})^{1+\sigma},$$ the sum being over the nonzero ideals $\mathfrak{n}$ prime to $S$ whose class is $\mathcal{C}$ and whose absolute norm is at most $Y$.
--
--   This is the lower-bound half of the class-by-class mean-square estimate for the Whittaker coefficients attached to a nonzero isotypic cuspidal vector on $\mathrm{GL}_2$ over $K$: the coefficients are expressed through the local Hecke recursion at each finite place, and the assertion is that along any ideal class supporting a nonzero recursion value the weighted mean-square sums grow at least linearly in the norm cut-off $Y$. It is used, together with the matching upper bound, in [`AutomorphicForm.exists_window_mass_le_mul_ample_window_mass_of_mem_isotypicCuspSubmodule`](thm.html#AutomorphicForm.exists_window_mass_le_mul_ample_window_mass_of_mem_isotypicCuspSubmodule), which compares the mass of a window with that of an amplified window.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_ClassSumGrowth_exists_forall_le_classSum_of_classCarriesMass.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory AutomorphicForm NumberField.AdelicHaar NumberField.AdelicBox
open NumberField.AdelicLevel
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel in

theorem
AutomorphicForm.ClassSumGrowth.exists_forall_le_classSum_of_classCarriesMass
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (σ : ℝ) (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ σ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S)
    (hSψ : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ differentIdeal ℤ (𝓞 K) → v ∈ S)
    (Ψ : HeckeEigensystem K ℂ)
    (hV : ∃ g ∈ isotypicCuspSubmodule K
        (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ, g ≠ 0) :
    ∃ cL : ℝ, 0 < cL ∧ ∃ Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ 𝒞 : ClassGroup (𝓞 K),
      (∃ 𝔫 : {𝔫 : Ideal (𝓞 K) // 𝔫 ≠ 0 ∧ ∀ v ∈ S, ¬ v.asIdeal ∣ 𝔫},
          ClassGroup.mk0 ⟨𝔫.1, mem_nonZeroDivisors_iff_ne_zero.mpr 𝔫.2.1⟩ = 𝒞 ∧
          (∏ᶠ v : HeightOneSpectrum (𝓞 K),
              UnramifiedWhittaker.heckeRecursionSeq (Ideal.absNorm v.asIdeal : ℂ) (Ψ.toRawCentral.a v)
                (Ψ.toRawCentral.b v) (emultiplicity v.asIdeal 𝔫.1).toNat) ≠ 0) →
      ∀ Y : ℝ, Y₀ ≤ Y →
        ENNReal.ofReal (cL * Y) ≤
          ∑' 𝔫 : {𝔫 : {𝔫 : Ideal (𝓞 K) // 𝔫 ≠ 0 ∧ ∀ v ∈ S, ¬ v.asIdeal ∣ 𝔫} //
              ClassGroup.mk0 ⟨𝔫.1, mem_nonZeroDivisors_iff_ne_zero.mpr 𝔫.2.1⟩ = 𝒞 ∧
                (Ideal.absNorm 𝔫.1 : ℝ) ≤ Y},
            (‖∏ᶠ v : HeightOneSpectrum (𝓞 K),
                UnramifiedWhittaker.heckeRecursionSeq (Ideal.absNorm v.asIdeal : ℂ) (Ψ.toRawCentral.a v)
                  (Ψ.toRawCentral.b v) (emultiplicity v.asIdeal 𝔫.1.1).toNat‖₊ : ℝ≥0∞) ^ 2 *
            ENNReal.ofReal ((Ideal.absNorm 𝔫.1.1 : ℝ) ^ (1 + σ)) := by sorry
