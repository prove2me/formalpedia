-- Prove2me | Theorems.Thm_AutomorphicForm_whittakerCoefficient_mul_heckeGen_pow_succ_mul_localRepInf_eq
-- name    : AutomorphicForm.whittakerCoefficient_mul_heckeGen_pow_succ_mul_localRepInf_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/9511d691-adbf-5cf3-b2bc-6c991a8d3337
-- title:
--   Central step-down of Whittaker coefficients along Hecke powers
-- statement:
--   Let $F$ be a number field, let `pins : CarrierPins F` be a carrier datum (a measurable space and measure on $\mathrm{GL}_2$ of the adeles, a domain $D$, a central subgroup $Z$, a family of level subgroups $U$, local elements `gen`, and a measurable space and measure $\nu$ on the adele ring $\mathbb{A}_F$), let $\psi$ be an additive character of $\mathbb{A}_F$ with values in $\mathbb{C}$, and let $v$ be a height-one prime of $\mathcal{O}_F$. Let $\varpi$ lie in the valuation ring of the completion at $v$, with nonzero image $\varpi$ in $F_v$, and assume `hgen`: the element $\mathrm{diag}(\varpi,1) \in \mathrm{GL}_2(F_v)$, placed at $v$ and the identity at all other finite places by `localEmbed` and then the identity at the infinite places by `finEmbed`, equals `heckeGen (𝓞 F) F v` (the image of the uniformiser unit at $v$ under `heckeGenAt`, the composite of `localUnit`, `Units.map (finIncl …)` and `diagOne`). Let $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ and $\chi : \mathbb{A}_F^{\times} \to \mathbb{C}$ satisfy the central law $\varphi(\mathrm{diag}(z,z)\,x) = \chi(z)\varphi(x)$ for all $z$ and $x$. Then for every $g \in \mathrm{GL}_2(\mathbb{A}_F)$ and every $e \in \mathbb{N}$, the Whittaker coefficient at $\alpha = 1$, namely $h \mapsto \int \varphi\left(\left(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\right) h\right)\,\psi(-x)\,d\nu(x)$, evaluated at $g \cdot \mathrm{heckeGen}_v^{\,e+1} \cdot \iota_v(w\,\mathrm{diag}(\varpi,1)\,w)$, where $w$ is the integral Weyl element `weylInt` and $\iota_v$ is the above embedding at $v$, equals $\chi(z_\varpi)$ times its value at $g \cdot \mathrm{heckeGen}_v^{\,e}$; here $z_\varpi$ is the idele unit equal to $\varpi$ at $v$ and to $1$ at all other finite places and at the infinite places.
--
--   This is the recursion step for the second Hecke coset representative at $v$: the product of the Hecke generator with $w\,\mathrm{diag}(\varpi,1)\,w$ is the central scalar $\varpi$ at $v$, so the associated Whittaker coefficient drops by one power of the Hecke generator at the cost of the central character value. It feeds the construction of cusp forms with nonvanishing Whittaker coefficient used in the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_whittakerCoefficient_mul_heckeGen_pow_succ_mul_localRepInf_eq.lean

import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm NumberField.AdelicLevel NumberField.AdelicBox AdelicDock LocalGL2

theorem AutomorphicForm.whittakerCoefficient_mul_heckeGen_pow_succ_mul_localRepInf_eq
    (F : Type) [Field F] [NumberField F] (pins : CarrierPins F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (v : HeightOneSpectrum (𝓞 F))
    (ϖ : v.adicCompletionIntegers F)
    (hϖ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0)
    (hgen : finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)) = heckeGen (𝓞 F) F v)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ → ℂ)
    (hcent : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (x : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F z * x) = χ z * φ x)
    (g : AdelicGL2 (𝓞 F) F) (e : ℕ) :
    whittakerCoefficient F pins ψ φ 1
        (g * heckeGen (𝓞 F) F v ^ (e + 1) * finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (localRepInf ϖ hϖ0))) =
      χ (Units.map (finIncl (𝓞 F) F : FiniteAdeleRing (𝓞 F) F →* AdeleRing (𝓞 F) F)
          (localUnit (𝓞 F) F v (Units.mk0 (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0))) *
        whittakerCoefficient F pins ψ φ 1 (g * heckeGen (𝓞 F) F v ^ e) := by sorry
