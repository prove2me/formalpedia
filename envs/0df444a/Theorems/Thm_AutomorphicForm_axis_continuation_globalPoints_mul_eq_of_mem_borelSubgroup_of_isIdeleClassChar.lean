-- Prove2me | Theorems.Thm_AutomorphicForm_axis_continuation_globalPoints_mul_eq_of_mem_borelSubgroup_of_isIdeleClassChar
-- name    : AutomorphicForm.axis_continuation_globalPoints_mul_eq_of_mem_borelSubgroup_of_isIdeleClassChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/b22b4f43-db9b-542d-ac3e-3b3035575864
-- title:
--   Rational Borel invariance of the continued adelic Eisenstein series
-- statement:
--   Let $F$ be a number field, with adele ring $\mathbb{A}=\mathbb{A}_F$ and $G=\mathrm{GL}_2(\mathbb{A})$, and let $\alpha_m\colon \mathbb{A}^\times\to\mathbb{R}^\times$ be the character obtained from the distributive Haar character `distribHaarChar` of $\mathbb{A}$ by pushing its $\mathbb{R}_{\ge 0}$-values into $\mathbb{R}$ and passing to units (the idelic modulus). Assume $\alpha_m$ takes strictly positive values, and let $\mu,\nu\colon\mathbb{A}^\times\to\mathbb{C}^\times$ be characters that are idele class characters in the sense that each is trivial on the image of $F^\times$. Let $\varphi\colon\mathbb{C}\to G\to\mathbb{C}$ be such that for every $s$ the function $\varphi_s$ is a section induced from the Borel subgroup for the pair $\eta_1(s)=\mu\cdot\alpha_m^{\,s+1/2}$, $\eta_2(s)=\nu\cdot\alpha_m^{-(s+1/2)}$, i.e. $\varphi_s(bg)=\eta_1(s)(b_{00})\,\eta_2(s)(b_{11})\,\varphi_s(g)$ for all $g\in G$ and all $b\in G$ with $b_{10}=0$, where $b_{00},b_{11}$ are the diagonal entries viewed as units. Let $O\subseteq\mathbb{C}$ be open and preconnected with $\{\operatorname{Re} s>1/2\}\subseteq O$, and let $E_c\colon\mathbb{C}\to G\to\mathbb{C}$ satisfy: for each $g\in G$ the function $s\mapsto E_c(s,g)$ is analytic on a neighbourhood of each point of $O$, and for $\operatorname{Re} s>1/2$ and all $g$, $$E_c(s,g)=\varphi_s(g)+\sum_{\xi\in F}\varphi_s\big(w\,n(\xi)\,g\big),$$ with $w$ the image in $G$ of the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ over $F$, $n(\xi)=\begin{pmatrix}1&\xi\\0&1\end{pmatrix}$ the image of the unipotent matrix attached to $\xi$, and the sum the unconditional sum (zero when the family fails to be summable). Then for every $s\in O$, every $\gamma\in\mathrm{GL}_2(F)$ with lower-left entry $\gamma_{10}=0$, and every $g\in G$, one has $E_c(s,\gamma g)=E_c(s,g)$, where $\gamma$ acts through the entrywise embedding $\mathrm{GL}_2(F)\to G$.
--
--   This is the elementary half of the automorphy of the $\mathrm{GL}_2$ Eisenstein series attached to a section induced from idele class characters: invariance under the rational Borel subgroup $B(F)$, proved in the region of absolute convergence and then propagated to the whole domain $O$ of analytic continuation by the identity theorem. It is used where the continued series is evaluated on the unitary axis, in the inner-product and truncation computation that cites it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_axis_continuation_globalPoints_mul_eq_of_mem_borelSubgroup_of_isIdeleClassChar.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.axis_continuation_globalPoints_mul_eq_of_mem_borelSubgroup_of_isIdeleClassChar
    (F : Type) [Field F] [NumberField F] :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμic : IsIdeleClassChar (𝓞 F) F μ) (_hνic : IsIdeleClassChar (𝓞 F) F ν)
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φ s))
      (O : Set ℂ) (Ec : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hO : IsOpen O) (_hOc : IsPreconnected O) (_hOhalf : {s : ℂ | 1 / 2 < s.re} ⊆ O)
      (_hEa : ∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Ec s g) O)
      (_hE : ∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Ec s g = φ s g + ∑' ξ : F, φ s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)),
    ∀ s ∈ O, ∀ γ ∈ borelSubgroup F, ∀ g : AdelicGL2 (𝓞 F) F,
      Ec s (globalPoints (𝓞 F) F γ * g) = Ec s g := by sorry
