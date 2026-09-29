-- Prove2me | Theorems.Thm_EisensteinGeneral_Glue_whittakerCoefficient_bruhatSeries_eq_finset_sum
-- name    : EisensteinGeneral.Glue.whittakerCoefficient_bruhatSeries_eq_finset_sum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/0561f957-e963-5ac5-b983-55f6ca47db3b
-- title:
--   Linearity of the Whittaker coefficient of a Bruhat series
-- statement:
--   Let $F$ be a number field, $\mathbb{A}$ its adele ring, and let $\psi$ be a continuous additive character of $\mathbb{A}$ with values of modulus $1$. Let $n$ be a natural number, $c : \mathrm{Fin}\,n \to \mathbb{C}$ a family of scalars, $\Psi_i : \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ a family of functions and $\Phi : \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$, subject to: for each $i$ there are homomorphisms $\chi_1, \chi_2 : \mathbb{A}^\times \to \mathbb{C}^\times$ with $\Psi_i$ an induced section for $(\chi_1,\chi_2)$, i.e. $\Psi_i(bg) = \chi_1(b_{00})\chi_2(b_{11})\Psi_i(g)$ for every $g$ and every $b$ in the adelic Borel subgroup (lower-left entry zero); and $\Phi(g') = \sum_i c_i \Psi_i(g')$ for all $g'$. Let $\xi \in F$ and $g \in \mathrm{GL}_2(\mathbb{A})$, and assume that for each $i$ the function $y \mapsto \Psi_i(w\,u(y)\,g)$ is integrable for the adelic additive Haar measure, where $w$ is the image of the Weyl element of $\mathrm{GL}_2(F)$ and $u(y) = \begin{pmatrix}1&y\\0&1\end{pmatrix}$. Then, writing $W(\varphi) = \int \varphi(u(x)g)\,\psi(-\xi x)\,d\nu(x)$ for the Whittaker coefficient at $(\xi,g)$ attached to the measure $\nu$ of `productionPins F` (the adelic Haar measure conditioned on the adelic box), one has $W\big(g' \mapsto \Phi(g') + \sum_{\xi' \in F} \Phi(w\,u(\xi')\,g')\big) = \sum_i c_i\, W\big(g' \mapsto \Psi_i(g') + \sum_{\xi' \in F} \Psi_i(w\,u(\xi')\,g')\big)$.
--
--   This records the linearity in the inducing data of the $\xi$-th Fourier–Whittaker coefficient of the Bruhat-type series attached to a section, for a finite complex combination of induced sections. It feeds the construction of the Euler-product identity for the Whittaker coefficients of the Bruhat Eisenstein series, [`AutomorphicForm.exists_unitaryChar_entire_partialEulerProduct_mul_eq_tsum_whittakerCoefficient_bruhatEisenstein`](thm.html#AutomorphicForm.exists_unitaryChar_entire_partialEulerProduct_mul_eq_tsum_whittakerCoefficient_bruhatEisenstein).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinGeneral_Glue_whittakerCoefficient_bruhatSeries_eq_finset_sum.lean

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPins
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain AutomorphicForm
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
set_option autoImplicit false

theorem EisensteinGeneral.Glue.whittakerCoefficient_bruhatSeries_eq_finset_sum (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψc : Continuous ψ) (hψ : ∀ x, ‖ψ x‖ = 1) (n : ℕ) (c : Fin n → ℂ)
    (Ψ : Fin n → AdelicGL2 (𝓞 F) F → ℂ) (Φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hΨ : ∀ i, ∃ χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ, IsInducedSection (𝓞 F) F χ₁ χ₂ (Ψ i))
    (hΦ : ∀ g', Φ g' = ∑ i : Fin n, c i * Ψ i g') (ξ : F) (g : AdelicGL2 (𝓞 F) F)
    (hint : ∀ i, Integrable (fun y => Ψ i (adelicWeyl (𝓞 F) F * unipotentGL2 y * g)) (adelicAddHaar (𝓞 F) F)) :
    whittakerCoefficient F (productionPins F) ψ
        (fun g' => Φ g' + ∑' ξ' : F, Φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g'))
        ξ g
      = ∑ i : Fin n, c i * whittakerCoefficient F (productionPins F) ψ
          (fun g' => Ψ i g' + ∑' ξ' : F,
            Ψ i (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ') * g')) ξ g := by sorry
