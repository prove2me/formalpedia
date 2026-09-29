-- Prove2me | Theorems.Thm_AutomorphicForm_integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj
-- name    : AutomorphicForm.integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/5f4e09f4-f2a4-55e6-8fd4-a80fecff9192
-- title:
--   Parseval identity for Whittaker coefficients on the adelic box
-- statement:
--   Let $F$ be a number field. Fix a subset $D \subseteq \mathrm{GL}_2(\mathbb{A}_F)$, a family $U$ of subgroups of $\mathrm{GL}_2(\mathbb{A}_F)$ indexed by the ideals of $\mathcal{O}_F$, and a map $\mathrm{gen}$ from the height-one spectrum of $\mathcal{O}_F$ to $\mathrm{GL}_2(\mathbb{A}_F)$; these data, together with the adelic box $B \subseteq \mathbb{A}_F$ (the points whose infinite part lies in the fundamental domain of the lattice basis in the mixed space and whose finite part is everywhere integral), assemble into the record `productionPinsOf F D U gen (adelicBox F)`, whose measure $\nu$ on $\mathbb{A}_F$ is the Borel Haar measure conditioned on $B$, and whose measure on $\mathrm{GL}_2(\mathbb{A}_F)$ is the Haar measure. Let $\psi$ be an additive character of $\mathbb{A}_F$ with values in $\mathbb{C}$ which is trivial on the image of $F$, continuous, and not identically $1$. Let $\varphi_1, \varphi_2 : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ and $g \in \mathrm{GL}_2(\mathbb{A}_F)$, and write $n(x)$ for the unipotent matrix $\begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix}$ and $W_\alpha(\varphi)(g) = \int \varphi(n(x)g)\,\psi(-\alpha x)\,d\nu(x)$ for the Whittaker coefficient at $\alpha \in F$. Assume: the slice $x \mapsto \varphi_1(n(x)g)$ is invariant under translation of $x$ by elements of $F$; both slices $x \mapsto \varphi_i(n(x)g)$ are continuous; the second slice is bounded in norm by some real constant; and $\alpha \mapsto \|W_\alpha(\varphi_1)(g)\|$ is summable over $F$. Then $$\int \varphi_1(n(x)g)\,\overline{\varphi_2(n(x)g)}\,d\nu(x) = \sum_{\alpha \in F} W_\alpha(\varphi_1)(g)\,\overline{W_\alpha(\varphi_2)(g)}.$$
--
--   This is Parseval's identity for the compact quotient $F \backslash \mathbb{A}_F$, realised on the adelic box with the conditioned Haar probability measure, applied to the unipotent slices of two functions on $\mathrm{GL}_2(\mathbb{A}_F)$. It is the inner integral of the Rankin–Selberg unfolding for $\mathrm{GL}_2 \times \mathrm{GL}_2$, and is used by the statements computing the Petersson integral of a form against a Bruhat–Eisenstein series as an integral of Whittaker coefficients, and by the variant that also bounds the sum of norms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj.lean

import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm NumberField.AdelicBox NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

theorem AutomorphicForm.integral_mul_conj_eq_tsum_whittakerCoefficient_mul_conj
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ₁ φ₂ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hper₁ : ∀ (β : F) (u : AdeleRing (𝓞 F) F),
      φ₁ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = φ₁ (unipotentGL2 u * g))
    (hcont₁ : Continuous fun x : AdeleRing (𝓞 F) F => φ₁ (unipotentGL2 x * g))
    (hcont₂ : Continuous fun x : AdeleRing (𝓞 F) F => φ₂ (unipotentGL2 x * g))
    (hbdd₂ : ∃ C : ℝ, ∀ x : AdeleRing (𝓞 F) F, ‖φ₂ (unipotentGL2 x * g)‖ ≤ C)
    (hsum₁ : Summable fun α : F =>
      ‖whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ₁ α g‖) :
    ∫ x, φ₁ (unipotentGL2 x * g) * (starRingEnd ℂ) (φ₂ (unipotentGL2 x * g))
        ∂(productionPinsOf F D U gen (adelicBox F)).ν =
      ∑' α : F, whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ₁ α g *
        (starRingEnd ℂ) (whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ₂ α g) := by sorry
