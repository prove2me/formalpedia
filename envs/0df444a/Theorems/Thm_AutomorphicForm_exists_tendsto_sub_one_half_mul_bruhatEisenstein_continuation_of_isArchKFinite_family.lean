-- Prove2me | Theorems.Thm_AutomorphicForm_exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family
-- name    : AutomorphicForm.exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/a3eadc8c-b40a-5714-849e-4d86cef5b1ea
-- title:
--   Pole at s=1/2 of the Bruhat–Eisenstein family on GL₂
-- statement:
--   Let $F$ be a number field and let $\alpha : (\mathbb{A}_F)^\times \to \mathbb{R}^\times$ be the character obtained from the distributive Haar character of $\mathbb{A}_F$ by passing through $\mathbb{R}_{\ge 0} \to \mathbb{R}$ and restricting to units; assume $\alpha(t) > 0$ for all $t$. Let $\varphi : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a family such that: for each $s$, $\varphi_s$ is an induced section for the pair of characters $\alpha^{s+1/2}$, $\alpha^{-(s+1/2)}$ (the trivial characters $\mu = \nu = 1$ being twisted by `cpowChar`), i.e. $\varphi_s(bg) = \alpha(b_{11})^{s+1/2}\alpha(b_{22})^{-(s+1/2)}\varphi_s(g)$ for $b$ in the adelic Borel subgroup; for each $s$ and each infinite place $w$ the right translates of $\varphi_s$ under the row-isometry subgroup at $w$ span a finite-dimensional space; each $\varphi_s$ is a smooth vector for the finite adelic $\mathrm{GL}_2$ subgroup; $(s,g) \mapsto \varphi_s(g)$ is jointly continuous; and $s \mapsto \varphi_s(g)$ is entire for each $g$. Then there exist $r \in \mathbb{C}$ and a real $a < 1/2$ such that, first, for every $g \in \mathrm{GL}_2(\mathbb{A}_F)$ there is $E' : \mathbb{C} \to \mathbb{C}$, meromorphic on all of $\mathbb{C}$ and analytic in a neighbourhood of every point of $\{\operatorname{re} s > a\} \setminus \{1/2\}$, satisfying $E'(s) = \varphi_s(g) + \sum_{\xi \in F} \varphi_s(w\,n(\xi)\,g)$ for $\operatorname{re} s > 1/2$ — where $w$ is the image of the Weyl element in $\mathrm{GL}_2(\mathbb{A}_F)$ and $n(\xi) = \begin{pmatrix}1 & \xi \\ 0 & 1\end{pmatrix}$ — and $(s - 1/2)E'(s) \to r$ as $s \to 1/2$ along the punctured neighbourhood filter; the same $r$ serves for all $g$. Secondly, $r \neq 0$ provided $\varphi_{1/2}$ takes non-negative real values at every $k$ whose finite part lies in `finiteIntegralGL2 (𝓞 F) F` and whose component at each infinite place $w$ satisfies `IsRowIsometry` (determinant of norm $1$ and preservation of $\lVert x\rVert^2 + \lVert y\rVert^2$ under the row action), and provided $\varphi_{1/2}(k) \neq 0$ for at least one such $k$.
--
--   This is the statement that the degenerate Eisenstein series attached to a spherical-parameter induced family on $\mathrm{GL}_2$ over $F$ continues past the line $\operatorname{re} s = 1/2$ with at worst a simple pole there whose residue is independent of the group variable, together with a non-vanishing criterion for that residue in terms of positivity of $\varphi_{1/2}$ on the maximal compact subgroup. It is used in the Rankin–Selberg part of the development, both for the Petersson-integral continuation statements and for the identification of the residue of the analytically continued Weyl intertwining integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology
open scoped NNReal

theorem AutomorphicForm.exists_tendsto_sub_one_half_mul_bruhatEisenstein_continuation_of_isArchKFinite_family
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g)),
    ∃ (r : ℂ) (a : ℝ), a < 1 / 2 ∧
      (∀ g : AdelicGL2 (𝓞 F) F, ∃ E' : ℂ → ℂ,
        MeromorphicOn E' Set.univ ∧
        AnalyticOnNhd ℂ E' ({s : ℂ | a < s.re} \ {(1 / 2 : ℂ)}) ∧
        (∀ s : ℂ, 1 / 2 < s.re →
          E' s = φ s g + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F *
            unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
        Tendsto (fun s : ℂ => (s - 1 / 2) * E' s) (𝓝[≠] (1 / 2 : ℂ)) (𝓝 r)) ∧
      ((∀ k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          0 ≤ (φ (1 / 2) k).re ∧ (φ (1 / 2) k).im = 0) →
        (∃ k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) ∧
          φ (1 / 2) k ≠ 0) →
        r ≠ 0) := by sorry
