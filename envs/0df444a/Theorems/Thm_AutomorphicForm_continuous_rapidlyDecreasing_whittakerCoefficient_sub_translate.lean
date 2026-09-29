-- Prove2me | Theorems.Thm_AutomorphicForm_continuous_rapidlyDecreasing_whittakerCoefficient_sub_translate
-- name    : AutomorphicForm.continuous_rapidlyDecreasing_whittakerCoefficient_sub_translate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/1ee7a3fb-9d7d-57a6-8268-9077b8993422
-- title:
--   Translation differences preserve automorphic shape data
-- statement:
--   Let $F$ be a number field, let $\varphi$ be a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $F$, and let $h$ be an adelic point of $\mathrm{GL}_2$; write $\widetilde\varphi(g)=\varphi(gh)-\varphi(g)$. The theorem is the conjunction of seven assertions about $\widetilde\varphi$. (1) If $\varphi$ is continuous, so is $\widetilde\varphi$. (2) If for all $c,u\in\mathbb{R}$ with $0<c$, all translating elements $t$ and all $N\in\mathbb{N}$ there is a bound $C$ with $\|\varphi(gt)\|\,(1+\mathrm{archHeight}_F(\mathrm{glArch}\,g))^N\le C$ for every $g$ in the integral windowed Siegel set of parameters $c,u$, then the same holds for $\widetilde\varphi$. (3) Left invariance $\varphi(\iota(\gamma)g)=\varphi(g)$ under all $\gamma\in\mathrm{GL}_2(F)$, $\iota$ being the entrywise map into the adeles, passes to $\widetilde\varphi$. (4) For every homomorphism $\omega$ from the ideles to $\mathbb{C}^\times$, the transformation law $\varphi(\mathrm{diag}(z,z)g)=\omega(z)\varphi(g)$ passes to $\widetilde\varphi$. (5) For every `CarrierPins` datum `pins` (bundling measurable spaces and measures, a region, a central subgroup, level subgroups and local generators), every additive character $\psi$ of the adeles, every $\alpha\in F$ and every $g$: if $x\mapsto\varphi(n(x)g')\psi(-\alpha x)$, with $n(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$, is $\mathrm{pins}.\nu$-integrable for $g'=gh$ and $g'=g$, then the corresponding integrand for $\widetilde\varphi$ at $g$ is integrable and its integral equals $W_\varphi(\alpha;gh)-W_\varphi(\alpha;g)$, where $W$ denotes that integral. (6) Under integrability at $gh$ and at $g$ for all $\alpha$, summability of $\alpha\mapsto\|W_\varphi(\alpha;gh)\|$ and of $\alpha\mapsto\|W_\varphi(\alpha;g)\|$ implies summability of $\alpha\mapsto\|W_{\widetilde\varphi}(\alpha;g)\|$. (7) Given types $\beta$ and $\gamma$ with a multiplication on $\gamma$, maps $r$ and $f$ into them, an element $h'\in\gamma$ and functions $W_A$, $W_f$, if $r(gh)=r(g)$ and $f(gh)=f(g)h'$ for all $g$, the Whittaker integrand for $\varphi$ at $\alpha$ is integrable at every $g$, and $W_\varphi(\alpha;g)=W_A(r(g))W_f(f(g))$ for all $g$, then $W_{\widetilde\varphi}(\alpha;g)=W_A(r(g))\bigl(W_f(f(g)h')-W_f(f(g))\bigr)$ for all $g$.
--
--   A bookkeeping package recording that the operator $\varphi\mapsto\varphi(\cdot\,h)-\varphi$ preserves the analytic and equivariance conditions in the definition of an automorphic form and acts on Whittaker coefficients by the corresponding difference, including the effect on a factorised (pure tensor) Whittaker function. It is used in the shaping step for the Rankin–Selberg integral, by [`AutomorphicForm.shapedRaw_bundle_sub_translate_unipotent_transl_rat`](thm.html#AutomorphicForm.shapedRaw_bundle_sub_translate_unipotent_transl_rat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_continuous_rapidlyDecreasing_whittakerCoefficient_sub_translate.lean

import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm LanglandsTunnell.RankinSelberg

theorem AutomorphicForm.continuous_rapidlyDecreasing_whittakerCoefficient_sub_translate
    (F : Type) [Field F] [NumberField F]
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (h : AdelicGL2 (𝓞 F) F) :
    ((Continuous φ → Continuous fun g => φ (g * h) - φ g) ∧
    (IsRapidlyDecreasingOnSiegelSets F φ → IsRapidlyDecreasingOnSiegelSets F fun g => φ (g * h) - φ g) ∧
    ((∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g) →
      ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
        (fun g => φ (g * h) - φ g) (globalPoints (𝓞 F) F γ * g) = (fun g => φ (g * h) - φ g) g) ∧
    (∀ ω : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ,
      (∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F), φ (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * φ g) →
      ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
        (fun g => φ (g * h) - φ g) (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * (fun g => φ (g * h) - φ g) g) ∧
    (∀ (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (α : F) (g : AdelicGL2 (𝓞 F) F),
      WhittakerCoefficientIntegrable F pins ψ φ α (g * h) → WhittakerCoefficientIntegrable F pins ψ φ α g →
        WhittakerCoefficientIntegrable F pins ψ (fun g => φ (g * h) - φ g) α g ∧
        whittakerCoefficient F pins ψ (fun g => φ (g * h) - φ g) α g =
          whittakerCoefficient F pins ψ φ α (g * h) - whittakerCoefficient F pins ψ φ α g) ∧
    (∀ (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (g : AdelicGL2 (𝓞 F) F),
      (∀ α : F, WhittakerCoefficientIntegrable F pins ψ φ α (g * h)) →
      (∀ α : F, WhittakerCoefficientIntegrable F pins ψ φ α g) →
      (Summable fun α : F => ‖whittakerCoefficient F pins ψ φ α (g * h)‖) →
      (Summable fun α : F => ‖whittakerCoefficient F pins ψ φ α g‖) →
        Summable fun α : F => ‖whittakerCoefficient F pins ψ (fun g => φ (g * h) - φ g) α g‖) ∧
    (∀ (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (α : F)
      {β γ : Type} [Mul γ] (r : AdelicGL2 (𝓞 F) F → β) (f : AdelicGL2 (𝓞 F) F → γ) (h' : γ)
      (WA : β → ℂ) (Wf : γ → ℂ),
      (∀ g : AdelicGL2 (𝓞 F) F, r (g * h) = r g) → (∀ g : AdelicGL2 (𝓞 F) F, f (g * h) = f g * h') →
      (∀ g : AdelicGL2 (𝓞 F) F, WhittakerCoefficientIntegrable F pins ψ φ α g) →
      (∀ g : AdelicGL2 (𝓞 F) F, whittakerCoefficient F pins ψ φ α g = WA (r g) * Wf (f g)) →
        ∀ g : AdelicGL2 (𝓞 F) F,
          whittakerCoefficient F pins ψ (fun g => φ (g * h) - φ g) α g = WA (r g) * (Wf (f g * h') - Wf (f g)))) := by sorry
