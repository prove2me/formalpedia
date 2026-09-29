-- Prove2me | Theorems.Thm_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary
-- name    : AutomorphicForm.summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/445f9ee0-c2b9-5efd-b9b5-6de23d8cdf42
-- title:
--   Summability of Whittaker coefficients of Bruhat Eisenstein series for Re s>1
-- statement:
--   Let $F$ be a number field and let $\alpha$ be the character of the idele group $(\mathbb{A}_F)^\times$ with values in $\mathbb{R}^\times$ obtained from the Haar-measure scaling character `distribHaarChar` of $\mathbb{A}_F$ by composing with the inclusion $\mathbb{R}_{\ge 0}\to\mathbb{R}$ and passing to units; assume $\alpha(x)>0$ for all $x$. Fix characters $\mu,\nu\colon(\mathbb{A}_F)^\times\to\mathbb{C}^\times$ with $\|\mu(x)\|=\|\nu(x)\|=1$ for all $x$, an additive character $\psi$ of $\mathbb{A}_F$ with values in $\mathbb{C}$ which satisfies the predicate `IsPrincipalInvariantAddChar`, is continuous and is non-trivial, and $s\in\mathbb{C}$ with $1<\mathrm{Re}\,s$. Let $\varphi\colon\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ satisfy: for every $b$ in `adelicBorel` and every $g$, $\varphi(bg)=\eta_1(b_{00})\,\eta_2(b_{11})\,\varphi(g)$, where $\eta_1=\mu\cdot\alpha^{s+1/2}$ and $\eta_2=\nu\cdot\alpha^{-(s+1/2)}$ (complex powers via `cpowChar`); for each infinite place $w$ of $F$ the right translates of $\varphi$ under `archRowIsometrySubgroup F w` span a finite-dimensional space; $\varphi$ is a smooth vector for the finite adelic subgroup of $\mathrm{GL}_2(\mathbb{A}_F)$; and $\varphi$ is continuous. Let $g\in\mathrm{GL}_2(\mathbb{A}_F)$ and put $E(g')=\varphi(g')+\sum_{\xi\in F}\varphi\bigl(w\,n(\xi)\,g'\bigr)$, with $w$ the adelic image of the Weyl element and $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$. Then the family $\xi\mapsto\int \bigl(E(n(x)g)\,\psi(-\iota(\xi)x)\bigr)\,d\nu(x)$, the Whittaker coefficients of $E$ at $g$ taken with respect to $\psi$ and the measure supplied by `productionPins F`, is summable over $\xi\in F$.
--
--   This is the convergence statement underlying the Fourier–Whittaker expansion along $F\backslash\mathbb{A}_F$ of the Bruhat-form Eisenstein series attached to a section of the adelic principal series induced from $(\mu\alpha^{s+1/2},\nu\alpha^{-(s+1/2)})$, in the range $\mathrm{Re}\,s>1$ and for unitary $\mu,\nu$. It is used by [`AutomorphicForm.bruhatEisenstein_eq_constantTerm_add_whittakerSum_of_one_lt_re_of_unitary`](thm.html#AutomorphicForm.bruhatEisenstein_eq_constantTerm_add_whittakerSum_of_one_lt_re_of_unitary), which decomposes the Eisenstein series into its constant term and the sum of its Whittaker coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPins

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open MeasureTheory NumberField NumberField.AdelicHaar
open AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.summable_whittakerCoefficient_bruhatEisenstein_of_one_lt_re_of_unitary
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
      (_hψ : IsGlobalAddChar F ψ)
      (s : ℂ) (_hs : 1 < s.re)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφK : IsArchKFinite F φ)
      (_hφf : IsKfSmooth F φ)
      (_hφc : Continuous φ)
      (g : AdelicGL2 (𝓞 F) F),
    let E : AdelicGL2 (𝓞 F) F → ℂ := fun g' =>
      φ g' + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F
        * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g')
    Summable (fun ξ : F => whittakerCoefficient F (productionPins F) ψ E ξ g) := by sorry
