-- Prove2me | Theorems.Thm_AutomorphicForm_rightConv_rightTranslate_mem_of_isCuspSubrep
-- name    : AutomorphicForm.rightConv_rightTranslate_mem_of_isCuspSubrep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/c7080011-4967-535e-900b-e74c7ffc04a5
-- title:
--   Cuspidal subrepresentations absorb smoothings of arbitrary right translates
-- statement:
--   Let $F$ be a number field, let `pins` be a choice of carrier data for $F$ (a measurable space and a measure on $\mathrm{GL}_2(\mathbb{A}_F)$, a subset $D$ of it, a subgroup $Z$ of the idele units, a family of level subgroups indexed by ideals of $\mathcal{O}_F$, a family of elements indexed by the finite places, and a measurable space and measure on $\mathbb{A}_F$), and let $\xi\colon Z\to\mathbb{C}^\times$ be a character of its centre subgroup. Let `tys` be an archimedean type family for $F$, assigning to each infinite place $w$ a natural number $\mathrm{card}(w)$ and to each index below it a finite-dimensional complex representation of the row-isometry subgroup of $\mathrm{GL}_2(F_w)$. Let $V$ be a $\mathbb{C}$-submodule of the functions $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ satisfying `IsCuspSubrep`: $V$ is contained in the span of those $\varphi$ all of whose right translates are smooth cuspidal automorphic at `pins` with central character $\xi$, which are continuous and which lie in the archimedean cut submodule of some archimedean type family; and $V$ is stable under right translation by the finite-adelic subgroup (the kernel of the archimedean projection), under right translation by the row-isometry subgroups at the infinite places, and under right convolution by every factorizable test function that is archimedean bi-finite for some type family. Let $\varphi\in V$, let $h\in\mathrm{GL}_2(\mathbb{A}_F)$ be arbitrary, and let $f\colon\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be a factorizable test function, i.e. a product of a compactly supported smooth function of the archimedean matrix entries with a locally constant compactly supported function of the finite component, and assume $f$ is archimedean bi-finite of types `tys`, meaning $x\mapsto f(x^{-1})$ lies in the archimedean cut submodule of `tys` and $f$ lies in the archimedean dual cut submodule of `tys`. Then the right convolution of the right translate $x\mapsto\varphi(xh)$ by $f$, namely $g\mapsto\int \varphi(gxh)\,f(x)\,dx$ against the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, again lies in $V$.
--
--   This extends the convolution stability built into the definition of a cuspidal subrepresentation from vectors of $V$ to arbitrary adelic right translates of them: the translate $x\mapsto\varphi(xh)$ itself generally leaves $V$, since it need not be finite for the archimedean row-isometry groups, but its smoothing by an archimedean bi-finite factorizable test function does not, the translation being absorbed into the test function by right invariance of the Haar measure. It is used in the approximation arguments for the cuspidal spectrum, where vectors of $V$ are approximated by smoothed translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_rightConv_rightTranslate_mem_of_isCuspSubrep.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.rightConv_rightTranslate_mem_of_isCuspSubrep
    (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspSubrep F pins ξ V)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ V)
    (h : AdelicGL2 (𝓞 F) F) (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : IsFactorizableTestFn F f) (hft : IsArchBiFinite F tys f) :
    rightConv F (rightTranslate F h φ) f ∈ V := by sorry
