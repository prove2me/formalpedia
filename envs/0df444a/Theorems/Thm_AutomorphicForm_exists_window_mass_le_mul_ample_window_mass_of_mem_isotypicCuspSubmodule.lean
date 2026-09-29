-- Prove2me | Theorems.Thm_AutomorphicForm_exists_window_mass_le_mul_ample_window_mass_of_mem_isotypicCuspSubmodule
-- name    : AutomorphicForm.exists_window_mass_le_mul_ample_window_mass_of_mem_isotypicCuspSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/617e3cf2-1ff8-5d16-bd8f-d478558125bc
-- title:
--   Siegel window mass bounded by ample window mass
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers with $0<c$ and $0<d_1$, and let $T$ be a finite set of points of $\mathrm{GL}_2(\mathbb{A}_K)$. Let $\alpha<\beta$ be reals with $0<\beta$, and let $\Phi_0\subseteq \mathrm{GL}_2(\mathbb{A}_K)$ be a measure-theoretic fundamental domain for the image of $\mathrm{GL}_2(K)$ under `globalPoints` acting on the slab $\{g : \mathrm{ideleNorm}_K(\det g)\in[\alpha,\beta]\}$, for the adelic Haar measure `adelicGLHaar` restricted to that slab. Let the carrier data be `productionPinsOf` with domain $\Phi_0$, level groups $N\mapsto \mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, Hecke generators `heckeGen`, and adelic box `adelicBox K`; its central subgroup is all of $(\mathbb{A}_K)^\times$, and $\xi$ is a character of it with values in $\mathbb{C}^\times$. Let $N\neq 0$ be an ideal of $\mathcal{O}_K$, $S$ a finite set of finite places, and $\Psi$ a Hecke eigensystem over $\mathbb{C}$. Then there exist $\kappa\geq 1$, a real $u'$ and a finite $C\in[0,\infty]$ such that every $g$ in the $\mathbb{C}$-span of the functions satisfying `IsIsotypicCuspFormAt` for these data (continuous, smooth cuspidal with central character $\xi$, right invariant under the level group at $N$, and with the Hecke and central eigenvalues prescribed by $\Psi$ outside $S$) obeys $$\int_{\bigcup_{x\in T}\,\Sigma\,x}\|g\|^2\,\le\,C\int_{\bigcup_{x\in T}\,\Sigma'\,x}\|g\|^2,$$ lower Lebesgue integrals against `adelicGLHaar`, where $\Sigma=\mathrm{centreCutSiegelSet}(c,u,d_1,d_2)$ and $\Sigma'=\mathrm{centreCutSiegelSetAmple}(c,u',d_1,d_2,\kappa)$ is the subset of $\mathrm{centreCutSiegelSet}(c,u',d_1,d_2)$ on which the local heights at any two infinite places differ by a factor at most $\kappa$.
--
--   This is the comparison step which replaces a centre-cut Siegel window by an "ample" one, in which the archimedean local heights are mutually comparable, at the cost of a finite multiplicative constant and enlarged parameters $u'$ and $\kappa$; the bound is uniform over the whole isotypic space of cusp forms. It is used by [`AutomorphicForm.exists_window_mass_le_mul_domain_mass_of_isArchKFinite_of_mem_isotypicCuspSubmodule`](thm.html#AutomorphicForm.exists_window_mass_le_mul_domain_mass_of_isArchKFinite_of_mem_isotypicCuspSubmodule), which converts window masses into masses over the fundamental domain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_window_mass_le_mul_ample_window_mass_of_mem_isotypicCuspSubmodule.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
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
    AutomorphicForm.exists_window_mass_le_mul_ample_window_mass_of_mem_isotypicCuspSubmodule
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (α β : ℝ) (hβ : 0 < β) (hαβ : α < β)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ) :
    ∃ κ : ℝ, 1 ≤ κ ∧ ∃ u' : ℝ, ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ g ∈ isotypicCuspSubmodule K
          (productionPinsOf K Φ₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
            (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξ N S Ψ,
        ∫⁻ x in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂, (‖g x‖₊ : ℝ≥0∞) ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
          ≤ C * ∫⁻ x in ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u' d₁ d₂ κ, (‖g x‖₊ : ℝ≥0∞) ^ 2
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
