-- Prove2me | Theorems.Thm_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary
-- name    : AutomorphicForm.norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/d1e1bbee-b029-50eb-b968-0c728e4254ce
-- title:
--   Polynomial decay of adelic Weyl–unipotent integrals, unitary twists
-- statement:
--   Let $F$ be a number field, and let $\alpha$ be the character of the idele group $(\mathbb{A}_F)^\times$ with values in $\mathbb{R}^\times$ obtained from the scaling factor `distribHaarChar` of the additive Haar measure of $\mathbb{A}_F$ by pushing its $\mathbb{R}_{\ge 0}$-values into $\mathbb{R}$ and passing to units. Assume $\alpha(x)>0$ for all $x$. Let $\mu,\nu\colon(\mathbb{A}_F)^\times\to\mathbb{C}^\times$ be characters with $|\mu(x)|=|\nu(x)|=1$ for all $x$; let $\psi$ be an additive character of $\mathbb{A}_F$ which is continuous, non-trivial, and invariant in the sense of `IsPrincipalInvariantAddChar`; let $s\in\mathbb{C}$ with $\operatorname{Re} s>1/2$. Let $\varphi\colon \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be continuous and satisfy, for every $b$ in the adelic Borel subgroup (lower-left entry zero) and every $g$, the relation $\varphi(bg)=\eta_1(b_{00})\,\eta_2(b_{11})\,\varphi(g)$ with $\eta_1=\mu\cdot\alpha^{s+1/2}$ and $\eta_2=\nu\cdot\alpha^{-(s+1/2)}$, the powers being complex powers of the positive reals $\alpha(\cdot)$; assume further that for each infinite place $w$ of $F$ the right translates of $\varphi$ by the subgroup `archRowIsometrySubgroup F w` span a finite-dimensional space. Then for every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ and every $N\in\mathbb{N}$ there is $C>0$ with $$\Big\|\int_{\mathbb{A}_F}\varphi\big(w\,n(y)\,g\big)\,\psi(-\xi y)\,dy\Big\|\le C\,(1+\|\Lambda\xi\|)^{-N}$$ for all $\xi\in F$, where $w$ is the image of the Weyl element under $\mathrm{GL}_2(F)\to\mathrm{GL}_2(\mathbb{A}_F)$, $n(y)=\begin{pmatrix}1&y\\0&1\end{pmatrix}$, $\xi$ is mapped into $\mathbb{A}_F$ by the structure map, the integral is against the adelic additive Haar measure, and $\Lambda$ is the mixed embedding of $F$.
--
--   This is the rapid-decay estimate for the Jacquet-type integral attached to a $K$-finite section of the principal series induced from unitary characters twisted by powers of the modulus character, with decay measured by the archimedean size of $\xi$. It feeds the summability of the Whittaker coefficients of the Bruhat–Eisenstein series, used in [`AutomorphicForm.summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary`](thm.html#AutomorphicForm.summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary.lean

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_ArchKFinite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MeasureTheory NumberField NumberField.AdelicHaar
open scoped NNReal

open scoped Classical in

theorem AutomorphicForm.norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
      (_hψ : IsGlobalAddChar F ψ)
      (s : ℂ) (_hs : 1 / 2 < s.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφK : IsArchKFinite F φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F) (N : ℕ),
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : F,
      ‖∫ y, φ (adelicWeyl (𝓞 F) F * unipotentGL2 y * g) *
          ψ (-(algebraMap F (AdeleRing (𝓞 F) F) ξ * y)) ∂(adelicAddHaar (𝓞 F) F)‖ ≤
        C * (1 + ‖NumberField.mixedEmbedding F ξ‖) ^ (-(N : ℝ)) := by sorry
