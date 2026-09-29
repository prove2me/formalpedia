-- Prove2me | Theorems.Thm_AutomorphicForm_integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient
-- name    : AutomorphicForm.integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/54b44ed2-967d-5e1d-bc7a-c4a57d623e58
-- title:
--   Rankin–Selberg unfolding along the rational torus on GL₂
-- statement:
--   Let $F$ be a number field and work in $\mathrm{GL}_2(\mathbb{A}_F)$, the general linear group of degree $2$ over the adele ring of $F$, with its Borel $\sigma$-algebra and Haar measure `adelicGLHaar`. Let $\mathcal{F}_B \subseteq \mathrm{GL}_2(\mathbb{A}_F)$ be a fundamental domain, for this Haar measure, for the image under the entrywise map `globalPoints` (induced by $F \to \mathbb{A}_F$) of the subgroup of $\mathrm{GL}_2(F)$ consisting of matrices whose $(1,0)$ entry vanishes, i.e. of the rational upper-triangular Borel. Let $k \colon \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be measurable and satisfy $k(hg) = k(g)$ for all $g$ and all $h$ in `rationalCentreUnipotent F`, the join of the subgroup of scalar matrices coming from $F^\times$ and the subgroup `adelicUnipotent F`. Assume the lower integral $\int^{-}_{\mathcal{F}_B} \sum_{a \in F^\times} \lVert k(\mathrm{diag}(a,1)\,g) \rVert_{e} \, dg$ is finite, $\mathrm{diag}(a,1)$ denoting the image under `globalPoints` of the diagonal matrix with entries $a,1$. Then: $q \mapsto k(q.\mathrm{out})$ is integrable on the orbit quotient of $\mathrm{GL}_2(\mathbb{A}_F)$ by `rationalCentreUnipotent F` for `rationalCentreUnipotentQuotientMeasure`; $q \mapsto \sum_{a \in F^\times} k(\mathrm{diag}(a,1)\,q.\mathrm{out})$ is integrable on the orbit quotient by `rationalTorusUnipotent F` for `rationalTorusUnipotentQuotientMeasure`; and both the integral of the latter over that quotient and the integral of the former over the centre–unipotent quotient equal $\int_{\mathcal{F}_B} \sum_{a \in F^\times} k(\mathrm{diag}(a,1)\,g) \, dg$. Here $q.\mathrm{out}$ is the chosen representative of the orbit $q$, and both quotient measures are the [`HaarQuotient.measure`](def/HaarQuotient.html#L28) attached to `adelicGLHaar` and to the respective Haar measures on the subgroups.
--
--   This is the torus step of the Rankin–Selberg unfolding for $GL_2$ over a number field: the sum over $\mathrm{diag}(a,1)$, $a \in F^\times$, converts an integral over the rational Borel quotient into an integral over the quotient by the rational centre times the adelic unipotent radical. It is used in the identification of the Petersson-type integral of a product with a Bruhat–Eisenstein series as an integral of Whittaker coefficients over the centre–unipotent quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient.lean

import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

theorem AutomorphicForm.integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient
    (F : Type) [Field F] [NumberField F]
    (𝓕B : Set (AdelicGL2 (𝓞 F) F))
    (h𝓕B : IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F)) 𝓕B (adelicGLHaar (Fin 2) (𝓞 F) F))
    (k : AdelicGL2 (𝓞 F) F → ℂ) (hk : Measurable k)
    (hkH : ∀ h ∈ rationalCentreUnipotent F, ∀ g : AdelicGL2 (𝓞 F) F, k (h * g) = k g)
    (hfin : ∫⁻ g in 𝓕B, ∑' a : Fˣ, ‖k (globalPoints (𝓞 F) F (diagOne a) * g)‖ₑ
      ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ∞) :
    Integrable (fun q : RationalCentreUnipotentQuotient F => k q.out) (rationalCentreUnipotentQuotientMeasure F) ∧
    Integrable (fun q : RationalTorusUnipotentQuotient F => ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * q.out))
      (rationalTorusUnipotentQuotientMeasure F) ∧
    ∫ q : RationalTorusUnipotentQuotient F, ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * q.out)
        ∂(rationalTorusUnipotentQuotientMeasure F) =
      ∫ g in 𝓕B, ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) ∧
    ∫ g in 𝓕B, ∑' a : Fˣ, k (globalPoints (𝓞 F) F (diagOne a) * g) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
      ∫ q : RationalCentreUnipotentQuotient F, k q.out ∂(rationalCentreUnipotentQuotientMeasure F) := by sorry
