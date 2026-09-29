-- Prove2me | Theorems.Thm_AutomorphicForm_WhittakerModel_forall_mem_localSpaceAt_scalar_mul_eq_localChar_mul
-- name    : AutomorphicForm.WhittakerModel.forall_mem_localSpaceAt_scalar_mul_eq_localChar_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/a2946ec8-c21b-5684-9298-fb69e927d55b
-- title:
--   Local Whittaker vectors at p inherit the central character
-- statement:
--   Fix the field $\mathbb{Q}$ with ring of integers $\mathcal{O}_{\mathbb{Q}}$, and let `pins` be a bundle `CarrierPins ℚ` of carrier data (a measurable space and a measure on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$, a subset $D$ of that group, a subgroup $Z$ of the idele units, a family $U$ of subgroups indexed by ideals of $\mathcal{O}_{\mathbb{Q}}$, a family `gen` of group elements indexed by finite places, and a measurable space and measure on the adele ring). Let $\psi$ be an additive character of $\mathbb{A}_{\mathbb{Q}}$ with values in $\mathbb{C}$, let $\varphi : \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ be any function, and let $\xi : \mathbb{A}_{\mathbb{Q}}^{\times} \to \mathbb{C}^{\times}$ be a group homomorphism. Assume `hcen`: for every unit idele $z$ and every $x \in \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ one has $\varphi(\mathrm{diag}(z,z)\, x) = \xi(z)\,\varphi(x)$. Let $p$ be a point of the height-one spectrum of $\mathcal{O}_{\mathbb{Q}}$. The conclusion is that every element $W$ of the $\mathbb{C}$-submodule of functions $\mathrm{GL}_2(\mathbb{Q}_p) \to \mathbb{C}$ spanned by those functions of the shape `localFnAt ℚ pins ψ p` applied to a right translate $x \mapsto \varphi(x h)$, $h \in \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ — that is, $g \mapsto$ the global Whittaker coefficient `whittakerCoefficient` of that translate, at index $1$, evaluated at the adelic matrix obtained by embedding $g$ at the place $p$ — satisfies $W(\mathrm{diag}(z,z)\, g) = (\mathrm{localChar}\,\xi\,p)(z)\, W(g)$ for all $z \in \mathbb{Q}_p^{\times}$ and $g \in \mathrm{GL}_2(\mathbb{Q}_p)$, where `localChar` $\xi$ $p$ sends $z$ to the value of $\xi$ on the idele that is $z$ at $p$ and $1$ at every other place, including the archimedean one.
--
--   This is the statement that the local Whittaker space at a finite place, built from the $\psi$-Whittaker coefficients of the right translates of an automorphic vector with central character $\xi$, consists of functions transforming under the centre of $\mathrm{GL}_2(\mathbb{Q}_p)$ through the local component $\xi_p$. It is used by the Rankin–Selberg computations of the converse-theorem part of the Langlands–Tunnell input, where local functional equations are applied place by place and each local slot must carry a known central character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WhittakerModel_forall_mem_localSpaceAt_scalar_mul_eq_localChar_mul.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.Analysis.MellinTransform
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open scoped nonZeroDivisors

theorem AutomorphicForm.WhittakerModel.forall_mem_localSpaceAt_scalar_mul_eq_localChar_mul
    (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hcen : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (x : AdelicGL2 (𝓞 ℚ) ℚ),
      φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * x) = ((ξ z : ℂˣ) : ℂ) * φ x)
    (p : HeightOneSpectrum (𝓞 ℚ)) :
    ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ pins ψ p φ,
      ∀ (z : (p.adicCompletion ℚ)ˣ) (g : GL (Fin 2) (p.adicCompletion ℚ)),
        W (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((localChar ξ p z : ℂˣ) : ℂ) * W g := by sorry
