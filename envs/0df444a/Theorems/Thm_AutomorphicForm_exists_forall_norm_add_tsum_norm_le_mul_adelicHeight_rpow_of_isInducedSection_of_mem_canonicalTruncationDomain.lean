-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_add_tsum_norm_le_mul_adelicHeight_rpow_of_isInducedSection_of_mem_canonicalTruncationDomain
-- name    : AutomorphicForm.exists_forall_norm_add_tsum_norm_le_mul_adelicHeight_rpow_of_isInducedSection_of_mem_canonicalTruncationDomain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/70890557-15eb-5242-bdbe-b188290f29cb
-- title:
--   Moderate growth of the absolute Bruhat series on the truncation domain
-- statement:
--   Let $F$ be a number field and let $\alpha,\beta$ be reals with $0<\alpha<\beta$. Write $\alpha_m\colon(\mathbb A_F)^\times\to\mathbb R^\times$ for the homomorphism obtained from the distributive Haar character of the adele ring of $F$ by composing with $\mathbb R_{\ge0}\to\mathbb R$ and passing to units. Assume $\alpha_m$ takes strictly positive values; let $\mu,\nu\colon(\mathbb A_F)^\times\to\mathbb C^\times$ be characters with $\|\mu(x)\|=\|\nu(x)\|=1$ and $\|\nu(x)\|=1$ for all $x$, let $s\in\mathbb C$ with $\operatorname{Re}s>1/2$, and let $\varphi\colon \mathrm{GL}_2(\mathbb A_F)\to\mathbb C$ be continuous and an induced section for the pair $\bigl(\mu\cdot\alpha_m^{\,s+1/2},\ \nu\cdot\alpha_m^{-(s+1/2)}\bigr)$, meaning that $\varphi(bg)=\eta_1(b_{11})\,\eta_2(b_{22})\,\varphi(g)$ for every $g$ and every $b$ in the adelic Borel subgroup (those invertible matrices with $b_{21}=0$), the powers of $\alpha_m$ being complex powers of positive reals. Then there exist reals $C\ge0$ and $A$ such that for every $g$ in the canonical truncation domain attached to $F,\alpha,\beta$ the family $\xi\mapsto\|\varphi(w\,n(\xi)\,g)\|$, indexed by $\xi\in F$, is summable, where $w$ is the image of the Weyl element $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $n(\xi)=\begin{pmatrix}1&\xi\\0&1\end{pmatrix}$, and moreover $\|\varphi(g)\|+\sum_{\xi\in F}\|\varphi(w\,n(\xi)\,g)\|\le C\cdot H_F(g)^A$, with $H_F$ the adelic height (the product of its archimedean and finite factors).
--
--   This is the majorant estimate for Eisenstein series in the $\mathrm{GL}_2$ setting: the absolute Bruhat series of a continuous induced section converges and grows at most polynomially in the adelic height on the canonical truncation domain. It is used to justify the absolutely convergent unfolding of integrals of an Eisenstein series against a cusp form, in the proof that the axis continuation is orthogonal to the cuspidal basis for $\operatorname{Re} s>1/2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_add_tsum_norm_le_mul_adelicHeight_rpow_of_isInducedSection_of_mem_canonicalTruncationDomain.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_NumberField_AdelicHeight
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHeight
open AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.exists_forall_norm_add_tsum_norm_le_mul_adelicHeight_rpow_of_isInducedSection_of_mem_canonicalTruncationDomain
    (F : Type) [Field F] [NumberField F] (α β : ℝ) (hα : 0 < α) (hαβ : α < β) :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (_hs : 1 / 2 < s.re) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) φ)
      (_hφc : Continuous φ),
    ∃ C A : ℝ, 0 ≤ C ∧ ∀ g ∈ AutomorphicForm.canonicalTruncationDomain F α β,
      Summable (fun ξ : F => ‖φ (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖) ∧
      ‖φ g‖ + ∑' ξ : F, ‖φ (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖ ≤ C * adelicHeight F g ^ A := by sorry
