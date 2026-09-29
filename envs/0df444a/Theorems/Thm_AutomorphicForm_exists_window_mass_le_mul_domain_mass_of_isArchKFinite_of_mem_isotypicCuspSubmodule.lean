-- Prove2me | Theorems.Thm_AutomorphicForm_exists_window_mass_le_mul_domain_mass_of_isArchKFinite_of_mem_isotypicCuspSubmodule
-- name    : AutomorphicForm.exists_window_mass_le_mul_domain_mass_of_isArchKFinite_of_mem_isotypicCuspSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/43eabe70-4d3e-52cd-9916-08d2b1378fe7
-- title:
--   Siegel window mass bounded by fundamental domain mass
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers with $0<c$ and $0<d_1$, let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$, and let $\alpha<\beta$ be reals with $0<\beta$. Let $\Phi_0\subseteq \mathrm{GL}_2(\mathbb{A}_K)$ be a measure-theoretic fundamental domain for the left action of the image of $\mathrm{GL}_2(K)$ under `globalPoints` on the norm slab $\{g\mid \|\det g\|_{\mathbb{A}}\in[\alpha,\beta]\}$, for the adelic Haar measure `adelicGLHaar` restricted to that slab, where $\|\cdot\|_{\mathbb{A}}$ is the idelic modulus given by the distributive Haar character. Let the carrier data be `productionPinsOf` for the domain $\Phi_0$, the level subgroups $N\mapsto \mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, the Hecke generators `heckeGen` at the finite places, and the adelic box; its central subgroup is all of $(\mathbb{A}_K)^\times$, and $\xi$ is a character of it with values in $\mathbb{C}^\times$. Let $N\neq 0$ be an ideal of $\mathcal{O}_K$, $S$ a finite set of finite places, and $\Psi$ a Hecke eigensystem over $\mathbb{C}$ (a nonzero level together with families $a,b$ indexed by the finite places). Then there is a constant $C<\infty$ in $[0,\infty]$, depending only on these data, such that every $g$ in the $\mathbb{C}$-span of the functions satisfying `IsIsotypicCuspFormAt` for these data which is archimedean $K$-finite (at each infinite place $w$ the right translates of $g$ under `archRowIsometrySubgroup` span a finite-dimensional space) satisfies $$\int_{\bigcup_{x\in T}\,\mathfrak{S}\cdot x}\|g\|^2\,d\mu \;\le\; C\int_{\Phi_0}\|g\|^2\,d\mu,$$ both lower Lebesgue integrals taken for `adelicGLHaar` and valued in $[0,\infty]$, where $\mathfrak{S}$ is the centre-cut Siegel set of parameters $c,u,d_1,d_2$ (finite part integral, local height at least $c$, $x$-window square at most $u^2$, and archimedean determinant norms in $[d_1,d_2]$ at every infinite place).
--
--   This is the quantitative comparison, for archimedean $K$-finite isotypic cusp forms, between the $L^2$-mass over a finite union of right translates of a centre-cut Siegel set and the $L^2$-mass over a fundamental domain for $\mathrm{GL}_2(K)$ on a determinant-norm slab; the constant is uniform over the space of forms. It is obtained from the analogous bound for the ample Siegel sets together with the uniform finiteness of the number of rational points translating a given adelic point into the ample window, and it feeds the approximation statement [`AutomorphicForm.exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre`](thm.html#AutomorphicForm.exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_window_mass_le_mul_domain_mass_of_isArchKFinite_of_mem_isotypicCuspSubmodule.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem
    AutomorphicForm.exists_window_mass_le_mul_domain_mass_of_isArchKFinite_of_mem_isotypicCuspSubmodule
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ g ∈ isotypicCuspSubmodule K
          (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ,
        IsArchKFinite K g →
          ∫⁻ x in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂, (‖g x‖₊ : ℝ≥0∞) ^ 2
              ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
            ≤ C * ∫⁻ x in Φ₀, (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
