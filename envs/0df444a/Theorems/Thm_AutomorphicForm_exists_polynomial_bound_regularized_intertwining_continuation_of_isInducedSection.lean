-- Prove2me | Theorems.Thm_AutomorphicForm_exists_polynomial_bound_regularized_intertwining_continuation_of_isInducedSection
-- name    : AutomorphicForm.exists_polynomial_bound_regularized_intertwining_continuation_of_isInducedSection
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/fa52248f-bb36-52d7-8d87-dbfd547e6581
-- title:
--   Regularised polynomial vertical bound for the continued intertwining operator
-- statement:
--   Let $F$ be a number field, let $\alpha$ be the module character $x \mapsto \mathrm{distribHaarChar}(\mathbf{A}_F)(x)$ of the idele group viewed in $\mathbb{R}^\times$, assumed pointwise positive, and let $\mu,\nu \colon \mathbf{A}_F^\times \to \mathbb{C}^\times$ be continuous characters that are unitary ($\|\chi(x)\|=1$ for all $x$) and trivial on the principal ideles coming from $F^\times$. Let $\varphi \colon \mathbb{C} \times \mathrm{GL}_2(\mathbf{A}_F) \to \mathbb{C}$ be such that each $\varphi_s$ satisfies $\varphi_s(bg) = \eta_1(b_1)\eta_2(b_2)\varphi_s(g)$ for $b$ in the adelic Borel subgroup with diagonal entries $b_1,b_2$, where $\eta_1 = \mu\,\alpha^{s+1/2}$ and $\eta_2 = \nu\,\alpha^{-(s+1/2)}$; each $\varphi_s$ is $K_\infty$-finite (at every infinite place $w$ the right translates under the row-isometry subgroup span a finite-dimensional space) and a smooth vector for the finite adelic $\mathrm{GL}_2$; $\varphi$ is jointly continuous and, for each $g$, entire in $s$; and at each infinite place there is a single finite-dimensional $\mathbb{C}$-subspace $W$ containing all functions $k \mapsto \varphi_s(gk)$ on the row-isometry subgroup, uniformly in $s$ and $g$. Let $Mc$ be such that, for each $g$, $s \mapsto Mc(s,g)$ is meromorphic in normal form on all of $\mathbb{C}$ and equals the Weyl intertwining integral $\int_{\mathbf{A}_F} \varphi_s(w^{-1}u(x)g)\,dx$ (adelic additive Haar measure) for $\mathrm{Re}\,s > 1/2$. Then for every $\sigma_0 > 0$ there exist $A \ge 0$ and $N \in \mathbb{N}$ such that for all $s$ with $0 \le \mathrm{Re}\,s \le \sigma_0$ and all $k$ in the adelic maximal compact subgroup (finite part integral, archimedean components row isometries): if $\mu\nu^{-1}$ equals the character $x \mapsto \|x\|^{i\tau}$ of the idele norm for some real $\tau$, then $\|(s - (1/2 - (\tau/2) i))\,Mc(s,k)\| \le A(1+|\mathrm{Im}\,s|)^N \sup_{k' \in \mathbf{K}} \|\varphi_s(k')\|$; and if $\mu\nu^{-1}$ is no such character, then $\|Mc(s,k)\| \le A(1+|\mathrm{Im}\,s|)^N \sup_{k' \in \mathbf{K}} \|\varphi_s(k')\|$.
--
--   This is the growth estimate in vertical strips for the meromorphically continued standard intertwining operator of the adelic principal series of $\mathrm{GL}_2$, in the form regularised by the factor $s - (1/2 - i\tau/2)$ that cancels the possible pole occurring when $\mu\nu^{-1}$ is a power of the idele norm. It is the form from which the unregularised polynomial bound [`AutomorphicForm.exists_polynomial_bound_intertwining_continuation_of_isInducedSection`](thm.html#AutomorphicForm.exists_polynomial_bound_intertwining_continuation_of_isInducedSection) is deduced, and it enters the analytic theory of Eisenstein series for $\mathrm{GL}_2$ over a number field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_polynomial_bound_regularized_intertwining_continuation_of_isInducedSection.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.Analysis.Meromorphic.NormalForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.exists_polynomial_bound_regularized_intertwining_continuation_of_isInducedSection
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
    ∃ A : ℝ, 0 ≤ A ∧ ∃ N : ℕ, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ σ₀ →
      ∀ k : AdelicGL2 (𝓞 F) F, k ∈ adelicMaximalCompact F →
        (∀ τ : ℝ, μ * ν⁻¹ = NumberField.TateGlobal.normPowChar F τ →
          ‖(s - ((1 / 2 : ℂ) - ((τ / 2 : ℝ) : ℂ) * Complex.I)) * Mc s k‖ ≤
            A * (1 + |s.im|) ^ N * ⨆ k' : ↥(adelicMaximalCompact F), ‖φ s (k' : AdelicGL2 (𝓞 F) F)‖) ∧
        ((∀ τ : ℝ, μ * ν⁻¹ ≠ NumberField.TateGlobal.normPowChar F τ) →
          ‖Mc s k‖ ≤
            A * (1 + |s.im|) ^ N * ⨆ k' : ↥(adelicMaximalCompact F), ‖φ s (k' : AdelicGL2 (𝓞 F) F)‖) := by sorry
