-- Prove2me | Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_continuation_bruhatEisenstein_sub_constantTerm_of_re_nonneg_of_isArchKFinite_family
-- name    : AutomorphicForm.exists_analyticOnNhd_continuation_bruhatEisenstein_sub_constantTerm_of_re_nonneg_of_isArchKFinite_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/4bd1a58e-63d1-5f41-a9ca-b5c548f3bb29
-- title:
--   Continuation of the non-constant part of the GL₂ Eisenstein family
-- statement:
--   Let $F$ be a number field, and let $\alpha$ be the character of the idele group $(\mathbb{A}_F)^\times$ obtained from the distributive Haar character `distribHaarChar` of the adele ring of $F$ by composing with the coercion $\mathbb{R}_{\ge 0}\to\mathbb{R}$ and passing to units, assumed to take strictly positive values (hypothesis $h\alpha$). Let $\mu,\nu:(\mathbb{A}_F)^\times\to\mathbb{C}^\times$ be monoid homomorphisms that are unitary ($|\mu(x)|=|\nu(x)|=1$ for all ideles $x$), trivial on the principal ideles coming from $F^\times$, and continuous as $\mathbb{C}$-valued functions. Let $\varphi:\mathbb{C}\to \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a family such that: for every $s$, $\varphi_s$ is an induced section for the pair $(\mu\cdot\alpha^{s+1/2},\ \nu\cdot\alpha^{-(s+1/2)})$, i.e. $\varphi_s(bg)=\chi_1(\mathrm{diag}_1 b)\chi_2(\mathrm{diag}_2 b)\varphi_s(g)$ for $b$ in the adelic Borel subgroup and all $g$; every $\varphi_s$ satisfies `IsArchKFinite` at each infinite place and is a smooth vector for right translation by the finite adelic $\mathrm{GL}_2$ subgroup; $(s,g)\mapsto\varphi_s(g)$ is jointly continuous; $s\mapsto\varphi_s(g)$ is entire for each $g$; and for each infinite place $w$ there is one finite-dimensional $\mathbb{C}$-subspace $W$ of functions on the row-isometry subgroup at $w$ containing $k\mapsto\varphi_s(gk)$ for all $s$ and $g$. Put $E_s(h)=\varphi_s(h)+\sum_{\xi\in F}'\varphi_s(w\,n(\xi)\,h)$, with $w$ the image of the Weyl element in $\mathrm{GL}_2(\mathbb{A}_F)$ and $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$, the adeles carrying their Borel $\sigma$-algebra. The assertion is that there exist an open set $U\subseteq\mathbb{C}$ containing the closed half-plane $\{\operatorname{Re} s\ge 0\}$ and a function $V:\mathbb{C}\to \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ such that $s\mapsto V_s(h)$ is analytic on a neighbourhood of $U$ for every $h$, $(s,h)\mapsto V_s(h)$ is continuous on $U\times\mathrm{univ}$, and for all $h$ and all $s$ with $\operatorname{Re} s>1/2$ one has $V_s(h)=E_s(h)-\mathrm{CT}(E_s)(h)$, where $\mathrm{CT}$ is the constant term along $t\mapsto n(t)$ taken against the adelic additive Haar measure conditioned on the adelic box.
--
--   This is the non-constant-term half of the holomorphic continuation of the adelic $\mathrm{GL}_2$ Eisenstein family attached to two unitary idele class characters: the difference between the Eisenstein series and its constant term along the unipotent radical extends analytically from $\operatorname{Re} s>1/2$ to an open set containing the closed half-plane $\operatorname{Re} s\ge 0$. It is combined with the continuation of the Weyl intertwining integral in [`AutomorphicForm.exists_analyticOnNhd_axis_continuation_bruhatEisenstein_weylIntertwiningIntegral_of_isArchKFinite_family`](thm.html#AutomorphicForm.exists_analyticOnNhd_axis_continuation_bruhatEisenstein_weylIntertwiningIntegral_of_isArchKFinite_family) to continue $E_s$ itself to a neighbourhood of the unitary axis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_analyticOnNhd_continuation_bruhatEisenstein_sub_constantTerm_of_re_nonneg_of_isArchKFinite_family.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.exists_analyticOnNhd_continuation_bruhatEisenstein_sub_constantTerm_of_re_nonneg_of_isArchKFinite_family
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hφKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φ s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W),
    letI := adeleBorel (𝓞 F) F
    let E : ℂ → AdelicGL2 (𝓞 F) F → ℂ := fun s h =>
      φ s h + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
        unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * h)
    ∃ (U : Set ℂ) (V : ℂ → AdelicGL2 (𝓞 F) F → ℂ),
      IsOpen U ∧ {s : ℂ | 0 ≤ s.re} ⊆ U ∧
      (∀ h : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => V s h) U) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => V p.1 p.2) (U ×ˢ Set.univ) ∧
      (∀ (s : ℂ) (h : AdelicGL2 (𝓞 F) F), 1 / 2 < s.re →
        V s h = E s h -
          constantTerm (ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
            (fun t => unipotentGL2 t) (E s) h) := by sorry
