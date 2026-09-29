-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
-- name    : AutomorphicForm.CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/6cf529a2-ab42-5f04-b7df-d10eaa480ee9
-- title:
--   Members of the K_∞-finite cuspidal span are continuous cusp forms
-- statement:
--   Let $K$ be a number field, let $D$ be a subset of $\mathrm{GL}_2(\mathbb{A}_K)$ (written `AdelicGL2 (𝓞 K) K`), let $U$ assign to each ideal of $\mathcal{O}_K$ a subgroup of $\mathrm{GL}_2(\mathbb{A}_K)$, and let $\mathrm{gen}$ assign to each height one prime of $\mathcal{O}_K$ an element of $\mathrm{GL}_2(\mathbb{A}_K)$; these data, together with the box $\mathtt{adelicBox } K$ (infinite part in the preimage of the fundamental domain of the Minkowski lattice basis, finite part the integral adeles), assemble into the carrier-pins bundle `productionPinsOf K D U gen (adelicBox K)`, whose measurable structures are the Borel ones, whose measure on $\mathrm{GL}_2(\mathbb{A}_K)$ is adelic Haar measure, whose central subgroup is all of $(\mathbb{A}_K)^\times$, and whose measure on $\mathbb{A}_K$ is additive Haar measure conditioned on that box. Let $\xi$ be a homomorphism from that (full) subgroup of ideles to $\mathbb{C}^\times$, and let $x : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ lie in the $\mathbb{C}$-span of the set of functions $\varphi$ that are continuous, satisfy `IsSmoothCuspAutomorphicFnAt` for every right translate $h \mapsto \varphi(hg)$, and lie in $\mathtt{archCutSubmodule}$ for some archimedean type family. Then $x$ is continuous and, for every $g \in \mathrm{GL}_2(\mathbb{A}_K)$, the translate $h \mapsto x(hg)$ again satisfies `IsSmoothCuspAutomorphicFnAt` for these pins and $\xi$, i.e. it satisfies `IsAutomorphicFnAt`, its constant term along `unipotentGL2` with respect to the conditioned adelic measure vanishes, and it is a smooth vector for the finite adelic subgroup of $\mathrm{GL}_2$ acting by right translation. The conclusion asserts nothing about membership in an archimedean type cut.
--
--   This records that the two conditions defining a $K_f$-smooth cusp automorphic function — continuity and cuspidality of all right translates — are linear, so they pass from the spanning vectors of the $K_\infty$-finite cuspidal space to arbitrary elements of the span, while the archimedean type condition need not. It is the basic tool allowing analytic statements about cusp forms to be applied to individual vectors of a cuspidal constituent, and is invoked throughout the subsequent study of cuspidal constituents (for instance in the results on right convolutions and on elements of archimedean cuts).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicBox AutomorphicForm AutomorphicForm.CuspidalConstituent IsDedekindDomain

theorem AutomorphicForm.CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (ξ : (productionPinsOf K D U gen (adelicBox K)).Z →* ℂˣ)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hx : x ∈ cuspKFiniteSubmodule K (productionPinsOf K D U gen (adelicBox K)) ξ) :
    Continuous x ∧ ∀ g : AdelicGL2 (𝓞 K) K,
      IsSmoothCuspAutomorphicFnAt K (productionPinsOf K D U gen (adelicBox K)) ξ (rightTranslate K g x) := by sorry
