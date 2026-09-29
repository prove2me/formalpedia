-- Prove2me | Theorems.Thm_AutomorphicForm_whittakerCoefficient_archRealLiftAt_mul_laws_and_torus_ode_of_archCasimirAt_eq_smul_rat
-- name    : AutomorphicForm.whittakerCoefficient_archRealLiftAt_mul_laws_and_torus_ode_of_archCasimirAt_eq_smul_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/a9b531cf-e2dc-5d5e-9b16-aef9cae3b1d7
-- title:
--   Whittaker transformation laws and torus ODE over ℚ
-- statement:
--   Fix a set $D \subseteq \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, an integer $k$, complex numbers $\lambda$, $e$, $\nu$ with $\nu^2 = 1/4 - \lambda$, and a continuous function $\varphi : \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ subject to: left invariance under the image of $\mathrm{GL}_2(\mathbb{Q})$; transformation by the character `archWeightCharℝ` of weight $k$ under the archimedean row-isometry subgroup, transported through the identification of the completion of $\mathbb{Q}$ at its infinite place with $\mathbb{R}$, in the sense of the predicate `HasArchCharacterAt₀`; archimedean smoothness, i.e. $e \mapsto \varphi(g \cdot \mathrm{archRealLiftAt}\, e)$ is $C^\infty$ on the invertible real $2 \times 2$ matrices for every $g$; a regularity hypothesis stating that for every finite list $l$ of directions $H, E, F$ the iterated flow-derivative $\mathrm{archDerivAt}$-fold of $\varphi$ along $l$ is continuous and, for all $0 < e_1 < e_2$, bounded on the shell where the idele norm of $\det g$ lies in $[e_1, e_2]$; the Casimir eigenvalue equation $-\bigl(\tfrac14 H^2 - \tfrac12 H + EF\bigr)\varphi = \lambda\varphi$ in the form $\mathrm{archCasimirAt}\,\varphi = \lambda \cdot \varphi$; and the central law $\varphi(\mathrm{diag}(t,t)_\infty \cdot g) = t^{e}\varphi(g)$ for real units $t > 0$. Let $g_0$ have trivial archimedean component, $\mathrm{glArch}(g_0) = 1$, and set $A(x) := W(x)$, the Whittaker coefficient at $\alpha = 1$ of $\varphi$ against the standard additive character of $\mathbb{A}_{\mathbb{Q}}$, evaluated at $\mathrm{archRealLiftAt}(x) \cdot g_0$; here the Whittaker coefficient is the integral $\int \varphi(u(x')g)\,\psi(-\alpha x')$ over the adele ring with respect to the additive Haar measure conditioned on the adelic box, the remaining data of the pins being the level subgroups $\mathrm{levelOne}(N) \sqcap \mathrm{finiteAdelicGL2Subgroup}$ and the Hecke generators $\mathrm{heckeGen}(v)$. The conclusion asserts four things: (i) $A(u(t)x) = e^{2\pi i t} A(x)$ for all real $t$ and all real $x$ with $\det x \neq 0$; (ii) $A(tx) = t^{e} A(x)$ for $t > 0$ and $\det x \neq 0$; (iii) $A(xr) = \mathrm{archWeightChar}_{\mathbb{R}}(k)(r)\, A(x)$ for $r$ in the real row-isometry subgroup $\mathrm{rowIsometrySubgroup}_0(\mathbb{R})$ and $x \in \mathrm{GL}_2(\mathbb{R})$; and (iv) for each $\varepsilon \in \{1,-1\}$, the torus function $f_\varepsilon(y) = A\bigl(\mathrm{diag}(\varepsilon\sqrt{y}, 1/\sqrt{y})\bigr)$ is differentiable on $(0,\infty)$, so is its derivative, it satisfies $y^2 f_\varepsilon''(y) + \bigl(\tfrac14 - \nu^2 + 2\pi\varepsilon k y - 4\pi^2 y^2\bigr) f_\varepsilon(y) = 0$ for all $y > 0$, and there are constants $C, N$ with $\|f_\varepsilon(y)\| \le C y^{N}$ for $y \ge 1$.
--
--   This packages the standard local behaviour of the first Whittaker coefficient of an automorphic function on $\mathrm{GL}_2$ over $\mathbb{Q}$: covariance under archimedean unipotents and positive scalars, the weight-$k$ rotation law, and Whittaker's differential equation with polynomial growth for the torus function. It is the archimedean input to the identification of the infinity-type of a weight-one Hecke eigensystem in the Langlands–Tunnell converse step, being used by [`LanglandsTunnell.archOccursInClassOf_whittakerCoefficient_fibre_eq_archW_or_twist_sign_of_archOccursInClassOf_rat`](thm.html#LanglandsTunnell.archOccursInClassOf_whittakerCoefficient_fibre_eq_archW_or_twist_sign_of_archOccursInClassOf_rat) and [`LanglandsTunnell.exists_whittakerCoefficient_fibre_eq_archW_mul_of_apply_mul_archRealGLAt_J_eq_mul_lower_of_mem_isCuspConstituent_weightOne_of_ne_bot`](thm.html#LanglandsTunnell.exists_whittakerCoefficient_fibre_eq_archW_mul_of_apply_mul_archRealGLAt_J_eq_mul_lower_of_mem_isCuspConstituent_weightOne_of_ne_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_whittakerCoefficient_archRealLiftAt_mul_laws_and_torus_ode_of_archCasimirAt_eq_smul_rat.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open LanglandsTunnell LanglandsTunnell.RealArchParam
open LanglandsTunnell.Converse

theorem AutomorphicForm.whittakerCoefficient_archRealLiftAt_mul_laws_and_torus_ode_of_archCasimirAt_eq_smul_rat
    (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (k : ℤ) (lam e ν : ℂ) (hν : ν ^ 2 = 1 / 4 - lam)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφc : Continuous φ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      φ (globalPoints (𝓞 ℚ) ℚ γ * g) = φ g)
    (hk : HasArchCharacterAt₀ ℚ Rat.infinitePlace ((archWeightCharℝ k).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal Rat.isReal_infinitePlace) (norm_ringEquivRealOfIsReal Rat.isReal_infinitePlace))) φ)
    (hsm : IsArchSmoothAt Rat.isReal_infinitePlace φ)
    (hreg : ∀ l : List ArchDir, Continuous (l.foldr (archDerivAt Rat.isReal_infinitePlace) φ) ∧
      ∀ e₁ e₂ : ℝ, 0 < e₁ → e₁ < e₂ → ∃ B : ℝ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc e₁ e₂ →
          ‖l.foldr (archDerivAt Rat.isReal_infinitePlace) φ g‖ ≤ B)
    (hΩ : archCasimirAt Rat.isReal_infinitePlace φ = lam • φ)
    (hcent : ∀ t : ℝˣ, (0 : ℝ) < (t : ℝ) → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      φ (adelicArchGLInclAt ℚ Rat.infinitePlace (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm.toRingHom
        (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) * g) = ((t : ℝ) : ℂ) ^ e * φ g)
    (g₀ : AdelicGL2 (𝓞 ℚ) ℚ) (hg₀ : glArch (𝓞 ℚ) ℚ g₀ = 1) :
    let A : Matrix (Fin 2) (Fin 2) ℝ → ℂ := fun x =>
      whittakerCoefficient ℚ (productionPinsOf ℚ D (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) (NumberField.StandardAddChar.stdAddChar ℚ) φ 1
        (archRealLiftAt Rat.isReal_infinitePlace (Matrix.of.symm x) * g₀)
    (∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), x.det ≠ 0 → A (ArchR.unip t * x) = ArchR.psi t * A x) ∧
    (∀ (t : ℝ) (x : Matrix (Fin 2) (Fin 2) ℝ), 0 < t → x.det ≠ 0 → A (t • x) = ((t : ℂ) ^ e) * A x) ∧
    (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
      A ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        (archWeightCharℝ k r : ℂ) * A (x : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    (∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      DifferentiableOn ℝ (fun y : ℝ => A !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]) (Set.Ioi 0) ∧
      DifferentiableOn ℝ (deriv (fun y : ℝ => A !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹])) (Set.Ioi 0) ∧
      (∀ y : ℝ, 0 < y →
        (y : ℂ) ^ 2 * deriv (deriv (fun y : ℝ => A !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹])) y
            + (1 / 4 - ν ^ 2 + 2 * (Real.pi : ℂ) * ((ε * k : ℝ) : ℂ) * (y : ℂ) - 4 * (Real.pi : ℂ) ^ 2 * (y : ℂ) ^ 2)
              * A !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹] = 0) ∧
      ∃ C N : ℝ, ∀ y : ℝ, 1 ≤ y → ‖A !![ε * Real.sqrt y, 0; 0, (Real.sqrt y)⁻¹]‖ ≤ C * y ^ N) := by sorry
