-- Prove2me | Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_sub_mul_bruhatEisenstein_norm_le_archHeight_pow_of_ne_of_isArchKFinite_family
-- name    : AutomorphicForm.exists_analyticOnNhd_sub_mul_bruhatEisenstein_norm_le_archHeight_pow_of_ne_of_isArchKFinite_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/6939508c-6ff0-59fd-ac9f-795ef132759b
-- title:
--   Moderate growth across the centre of a continued Eisenstein family
-- statement:
--   Let $F$ be a number field, and let $\alpha : (\mathbb{A}_F)^\times \to \mathbb{R}^\times$ be the character obtained from the module character `distribHaarChar` of the adele ring by passing from $\mathbb{R}_{\ge 0}$ to $\mathbb{R}$ and into the units, assumed (hypothesis $h\alpha$) to take strictly positive real values. Let $\mu,\nu : (\mathbb{A}_F)^\times \to \mathbb{C}^\times$ be characters that are unitary, i.e. $|\mu(x)| = |\nu(x)| = 1$ for all $x$, and trivial on the principal ideles $F^\times$, with $\mu \neq \nu$. Let $\varphi : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be such that, for every $s$, $\varphi_s$ satisfies the induced-section identity $\varphi_s(bg) = \eta_1(b_{00})\,\eta_2(b_{11})\,\varphi_s(g)$ for $b$ in the adelic Borel subgroup, where $\eta_1 = \mu\cdot\alpha^{s+1/2}$ and $\eta_2 = \nu\cdot\alpha^{-(s+1/2)}$ (the characters `etaFst` and `etaSnd`); for every $s$, $\varphi_s$ is archimedean $K$-finite, its right translates under the subgroup `archRowIsometrySubgroup` at each infinite place of $F$ spanning a finite-dimensional space, and $\varphi_s$ is a smooth vector for the finite adelic subgroup; $(s,g)\mapsto\varphi_s(g)$ is jointly continuous; and $s \mapsto \varphi_s(g)$ is entire for each $g$. Then there are a real $a < 1/2$, a complex $s_0 \neq 1/2$ and $G : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ such that: for each $g$, $s \mapsto G(s,g)$ is analytic on a neighbourhood of each point of $\{\operatorname{re} s > a\}$; for $\operatorname{re} s > 1/2$ and all $g$, $$G(s,g) = (s - s_0)\Bigl(\varphi_s(g) + \sum_{\xi \in F} \varphi_s\bigl(w\,n(\xi)\,g\bigr)\Bigr),$$ with $w$ the image of the Weyl element in $\mathrm{GL}_2(\mathbb{A}_F)$ and $n(\xi) = \begin{pmatrix}1&\xi\\0&1\end{pmatrix}$ for $\xi$ viewed in $\mathbb{A}_F$; $(s,g) \mapsto G(s,g)$ is continuous on $\{\operatorname{re} s > a\} \times \mathrm{GL}_2(\mathbb{A}_F)$; and for all reals $c > 0$ and $u$, every $t \in \mathrm{GL}_2(\mathbb{A}_F)$ and every compact $C \subseteq \{\operatorname{re} s > a\}$ there are $M \in \mathbb{R}$ and $N \in \mathbb{N}$ with $\|G(s, g t)\| \le M\,(1 + H_\infty(g))^N$ for all $s \in C$ and all $g$ in the integral windowed Siegel set of parameters $c,u$, that is, all $g$ whose finite part is integral, whose archimedean height $H_\infty(g) = \prod_v \mathrm{localHeight}(g_v)^{[F_v:\mathbb{R}]}$ is at least $c$, and whose window quantity `xWindowSq` at each infinite place is at most $u^2$.
--
--   This is the meromorphic continuation of the $\mathrm{GL}_2$ Eisenstein series attached to a pair of distinct unitary idele-class characters, in the form of a holomorphic family $G$ on a half-plane crossing the centre $s = 1/2$ obtained by clearing at most one simple pole at $s_0$, together with growth on Siegel sets that is polynomial in the archimedean height, uniformly for $s$ in compacta. It feeds the construction of Rankin–Selberg test data, being cited by [`AutomorphicForm.RankinSelberg.exists_testData_analyticOnNhd_sub_mul_peterssonIntegral_and_hasProd_rsEulerPoly_pair`](thm.html#AutomorphicForm.RankinSelberg.exists_testData_analyticOnNhd_sub_mul_peterssonIntegral_and_hasProd_rsEulerPoly_pair).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_analyticOnNhd_sub_mul_bruhatEisenstein_norm_le_archHeight_pow_of_ne_of_isArchKFinite_family.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_WindowedSiegelSet
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology
open scoped NNReal

theorem AutomorphicForm.exists_analyticOnNhd_sub_mul_bruhatEisenstein_norm_le_archHeight_pow_of_ne_of_isArchKFinite_family
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμF : IsIdeleClassChar (𝓞 F) F μ) (_hνF : IsIdeleClassChar (𝓞 F) F ν)
      (_hne : μ ≠ ν)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g)),
    ∃ (a : ℝ) (s₀ : ℂ) (G : ℂ → AdelicGL2 (𝓞 F) F → ℂ), a < 1 / 2 ∧ s₀ ≠ 1 / 2 ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => G s g) {s : ℂ | a < s.re}) ∧
      (∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F), 1 / 2 < s.re →
        G s g = (s - s₀) * (φ s g + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
          unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => G p.1 p.2)
        ({s : ℂ | a < s.re} ×ˢ Set.univ) ∧
      (∀ (c u : ℝ) (t : AdelicGL2 (𝓞 F) F) (C : Set ℂ), 0 < c → IsCompact C → C ⊆ {s : ℂ | a < s.re} →
        ∃ (M : ℝ) (N : ℕ), ∀ s ∈ C, ∀ g ∈ integralWindowedSiegelSet F c u,
          ‖G s (g * t)‖ ≤ M * (1 + archHeight F (glArch (𝓞 F) F g)) ^ N) := by sorry
