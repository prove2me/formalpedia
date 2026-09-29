-- Prove2me | Theorems.Thm_AutomorphicForm_WhittakerModel_localSpaceAt_comp_mul_right_mem
-- name    : AutomorphicForm.WhittakerModel.localSpaceAt_comp_mul_right_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/1094bbf2-1eae-55f8-956a-d10684fc27c0
-- title:
--   Right-translation stability of the local Whittaker space at p
-- statement:
--   Fix a bundle of data `pins : CarrierPins ℚ` over $\mathbb{Q}$ (a measurable space and a measure on $\mathrm{GL}_2$ of the adeles, a subset $D$, a subgroup $Z$ of the adelic units, a family $U$ of subgroups indexed by ideals of $\mathbb{Z}$, a family `gen` of adelic matrices indexed by the height-one primes, and a measurable space and measure on the adele ring), an additive character $\psi$ of the adele ring of $\mathbb{Q}$ with values in $\mathbb{C}$, a height-one prime $p$ of $\mathcal{O}_{\mathbb{Q}}$, and an arbitrary function $\varphi$ from $\mathrm{GL}_2$ of the adele ring to $\mathbb{C}$ (no automorphy, measurability or growth condition is imposed). By definition, `localSpaceAt ℚ pins ψ p φ` is the $\mathbb{C}$-submodule of functions $\mathrm{GL}_2(\mathbb{Q}_p) \to \mathbb{C}$ spanned by those $W$ of the form $g \mapsto \mathrm{whittakerCoefficient}\,\mathbb{Q}\,\mathrm{pins}\,\psi\,(x \mapsto \varphi(x h))\,1$ evaluated at the image of $g$ under the one-place embedding $\mathrm{GL}_2(\mathbb{Q}_p) \to \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ given by [`AdelicDock.finEmbed`](def/AdelicDock_LocalEmbedding.html#L145) composed after [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97), as $h$ ranges over $\mathrm{GL}_2$ of the adele ring. The assertion is that this submodule is stable under right translation: for every $W$ in it and every $h \in \mathrm{GL}_2(\mathbb{Q}_p)$, the function $g \mapsto W(gh)$ again lies in it.
--
--   This is the right-translation stability of the local Whittaker space at a finite place, in the form needed to regard it as a representation of $\mathrm{GL}_2(\mathbb{Q}_p)$ by right translation. It is used as the stability input for the local Whittaker/Kirillov constructions at $p$, and is cited by [`AutomorphicForm.shapedRaw_bundle_sub_translate_unipotent_transl_rat`](thm.html#AutomorphicForm.shapedRaw_bundle_sub_translate_unipotent_transl_rat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_WhittakerModel_localSpaceAt_comp_mul_right_mem.lean

import Definitions.Def_AutomorphicForm_WhittakerModelMultiplicityOne
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_StandardGlobalAddCharRat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm

theorem AutomorphicForm.WhittakerModel.localSpaceAt_comp_mul_right_mem
    (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) :
    ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ pins ψ p φ,
      ∀ h : GL (Fin 2) (p.adicCompletion ℚ), (fun g => W (g * h)) ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ pins ψ p φ := by sorry
