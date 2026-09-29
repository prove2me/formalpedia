-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_archTypeFamily_mem_archCutSubmodule_of_mem_isCuspConstituent
-- name    : AutomorphicForm.CuspidalConstituent.exists_archTypeFamily_mem_archCutSubmodule_of_mem_isCuspConstituent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/f72c45c4-21fa-57f4-b95a-5c0d2ebc81c5
-- title:
--   Every vector of a cuspidal constituent lies in an archimedean cut
-- statement:
--   Fix the base field $\mathbb{Q}$ and the package of carrier data `productionPinsGeneral ℚ` (the `CarrierPins` built from the Siegel-set representative region with parameters $c=1/2$, $u=1$, $d_1=1/2$, $d_2=2$, the level subgroups $\mathrm{levelOne}\sqcap\mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators `heckeGen`, and the adelic box data). Let $\xi$ be a homomorphism from the subgroup $Z\le(\mathbb{A}_{\mathbb{Q}}^{\times})$ recorded in those data to $\mathbb{C}^{\times}$, and let $V$ be a $\mathbb{C}$-submodule of the functions $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ which is a cuspidal constituent for $\xi$, i.e. $V$ is contained in `cuspKFiniteSubmodule ℚ (productionPinsGeneral ℚ) ξ`, is stable under right translation by elements of `finiteAdelicGL2Subgroup`, under right translation by $\mathrm{rowIsometryInclAt}_0$ of elements of $\mathrm{rowIsometrySubgroup}_0$ at each infinite place, and under right convolution with factorizable test functions that are archimedean bi-finite for some type family; moreover $V\neq 0$ and every such subrepresentation $W\le V$ is $0$ or $V$. Then for every $\varphi\in V$ there is an `ArchTypeFamily ℚ` $\mathrm{tys}$ — a number $\mathrm{card}(w)$ of archimedean types $\mathrm{rep}(w,i)$ at each infinite place $w$ — such that $\varphi$ lies in $\mathrm{archCutSubmodule}(\mathrm{tys})$, the intersection over all infinite places $w$ of the sums $\bigvee_{i<\mathrm{card}(w)}$ of the type submodules cut out by the representations $\mathrm{rep}(w,i).\rho$ along $\mathrm{rowIsometryInclAt}_0$.
--
--   This is the statement that vectors of a cuspidal constituent over $\mathbb{Q}$ are $K_\infty$-finite, in the concrete form that each such vector is annihilated-down to a finite archimedean type family at every infinite place. It is used in the Langlands–Tunnell strand, where an archimedean character is extracted for a cuspidal constituent with nonvanishing Whittaker coefficient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_archTypeFamily_mem_archCutSubmodule_of_mem_isCuspConstituent.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.Analysis.MellinTransform
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace LanglandsTunnell.RealArchParam
open scoped nonZeroDivisors

theorem AutomorphicForm.CuspidalConstituent.exists_archTypeFamily_mem_archCutSubmodule_of_mem_isCuspConstituent
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hV : CuspidalConstituent.IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ V)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφV : φ ∈ V) :
    ∃ tys : ArchTypeFamily ℚ, φ ∈ archCutSubmodule ℚ tys := by sorry
