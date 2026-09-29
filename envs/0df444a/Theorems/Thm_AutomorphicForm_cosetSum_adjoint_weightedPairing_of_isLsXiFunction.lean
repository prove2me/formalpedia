-- Prove2me | Theorems.Thm_AutomorphicForm_cosetSum_adjoint_weightedPairing_of_isLsXiFunction
-- name    : AutomorphicForm.cosetSum_adjoint_weightedPairing_of_isLsXiFunction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/4e300825-5587-5981-8b02-e0673557b944
-- title:
--   Adjointness of double-coset translate sums for the weighted pairing
-- statement:
--   Let $K$ be a number field, let $\alpha,\beta\in\mathbb{R}$ with $0<\alpha$, and let $\Phi_0\subseteq \mathrm{GL}_2(\mathbb{A}_K)$ be contained in the slab of $g$ with $\|\det g\|\in[\alpha,\beta]$, where $\|\cdot\|$ is the idele norm given by the distributive Haar character; assume $\Phi_0$ is a fundamental domain for the left action of the image of $\mathrm{GL}_2(K)$ under [`AutomorphicForm.globalPoints`](def/AutomorphicForm_AdelicLsXi.html#L15) on the adelic Haar measure `adelicGLHaar` restricted to that slab. Let $\xi$ be a homomorphism from the full group of ideles (as the subgroup $\top$) to $\mathbb{C}^\times$ and $\sigma\in\mathbb{R}$ with $\|\xi(z)\|=\|z\|^{\sigma}$, and let $U\le \mathrm{GL}_2(\mathbb{A}_K)$ satisfy $\|\det u\|^{\sigma}=1$ for $u\in U$. Let $\varphi,\psi:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous, invariant on the left under $\mathrm{GL}_2(K)$ and satisfying $\varphi(\mathrm{diag}(z,z)g)=\xi(z)\varphi(g)$ for all ideles $z$ (likewise $\psi$), square-integrable on $\Phi_0$, and right $U$-invariant. Let $g_v\in \mathrm{GL}_2(\mathbb{A}_K)$, let $r_0,\dots,r_{n-1}$ be any finite family with each $r_i\in Ug_vU$ (no exhaustion or distinctness assumed), and let $c$ be an idele with $g_v^{-1}\in \mathrm{diag}(c,c)\,Ug_vU$. Then $x\mapsto\sum_i\varphi(xr_i)$ and $x\mapsto\sum_i\psi(xr_i)$ are square-integrable on $\Phi_0$, and $$\int_{\Phi_0}\Big(\sum_i\varphi(xr_i)\Big)\overline{\psi(x)}\,\|\det x\|^{-\sigma}dx=\|\det g_v\|^{\sigma}\,\overline{\xi(c)}\int_{\Phi_0}\varphi(x)\overline{\sum_i\psi(xr_i)}\,\|\det x\|^{-\sigma}dx,$$ with the same family $(r_i)$ on both sides.
--
--   This is the adjointness, for the weighted Petersson pairing on a slab fundamental domain, of the operator formed by summing right translates over elements of a double coset $Ug_vU$ — the adelic shape of a Hecke operator at a place, with $U$ the level subgroup and $g_v$ the generator — the adjoint being the same operator times the scalar $\|\det g_v\|^{\sigma}\overline{\xi(c)}$. It is used in the later analysis of traces and fibre sums of such translate operators, for instance in [`AutomorphicForm.fibreSum_twistedCutTrace_eq_const_mul_fibreSum_cutTrace_of_centralElliptic_of_prime`](thm.html#AutomorphicForm.fibreSum_twistedCutTrace_eq_const_mul_fibreSum_cutTrace_of_centralElliptic_of_prime) and [`AutomorphicForm.summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre`](thm.html#AutomorphicForm.summable_norm_cutTrace_of_isUnitFactorizableOfTypeAt_of_coversModCentre), and it derives from the corresponding identity for a single right translate, [`AutomorphicForm.rightTranslate_adjoint_weightedPairing_of_isLsXiFunction`](thm.html#AutomorphicForm.rightTranslate_adjoint_weightedPairing_of_isLsXiFunction).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_cosetSum_adjoint_weightedPairing_of_isLsXiFunction.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar
open scoped ComplexConjugate BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.cosetSum_adjoint_weightedPairing_of_isLsXiFunction
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α)
    (Φ₀ : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (hΦ₀ : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hFD : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (σ : ℝ)
    (hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
      ‖((ξ z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ)
    (U : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (hU : ∀ u ∈ U, NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det u) ^ σ = 1)
    (φ ψ : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : AutomorphicForm.IsLsXiFunction (𝓞 K) K ⊤ ξ φ) (hψ : AutomorphicForm.IsLsXiFunction (𝓞 K) K ⊤ ξ ψ)
    (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφ₂ : MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀))
    (hψ₂ : MemLp ψ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀))
    (hφU : ∀ g : AutomorphicForm.AdelicGL2 (𝓞 K) K, ∀ u ∈ U, φ (g * u) = φ g)
    (hψU : ∀ g : AutomorphicForm.AdelicGL2 (𝓞 K) K, ∀ u ∈ U, ψ (g * u) = ψ g)
    (gv : AutomorphicForm.AdelicGL2 (𝓞 K) K) (n : ℕ) (reps : Fin n → AutomorphicForm.AdelicGL2 (𝓞 K) K)
    (hreps : ∀ i, ∃ u ∈ U, ∃ u' ∈ U, reps i = u * gv * u')
    (c : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ))
    (hc : ∃ u ∈ U, ∃ u' ∈ U,
      gv⁻¹ = AutomorphicForm.centralScalar (𝓞 K) K (c : (AdeleRing (𝓞 K) K)ˣ) * (u * gv * u')) :
    MemLp (fun x => ∑ i, φ (x * reps i)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) ∧
    MemLp (fun x => ∑ i, ψ (x * reps i)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) ∧
    ∫ x in Φ₀, (∑ i, φ (x * reps i)) * conj (ψ x) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det gv) ^ σ : ℝ) : ℂ) *
        conj ((ξ c : ℂˣ) : ℂ) *
        ∫ x in Φ₀, φ x * conj (∑ i, ψ (x * reps i)) *
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
