-- Prove2me | Theorems.Thm_AutomorphicForm_finiteDimensional_span_translates_of_mem_archCutSubmodule
-- name    : AutomorphicForm.finiteDimensional_span_translates_of_mem_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/6bc973d6-4f2e-568b-973d-6e5961734e19
-- title:
--   Finite-dimensional stable span of archimedean translates
-- statement:
--   Let $F$ be a number field. Let $\mathcal K = \prod_{w \mid \infty}$ `rowIsometrySubgroup₀ w.Completion`, the product over the infinite places $w$ of $F$ of the subgroups `rowIsometrySubgroup₀ w.Completion` of $GL_2(F_w)$, and let $\iota : \mathcal K \to GL_2(\mathbb A_{F,\infty})$ be a group homomorphism into $GL_2$ of the infinite adele ring such that for every $\kappa \in \mathcal K$ and every infinite place $w$ the image of $\iota\kappa$ under `archComponent`, i.e. under the map on $GL_2$ induced by evaluation at $w$, is the element $\kappa w$ viewed in $GL_2(F_w)$; thus $\iota$ places each component at its own place. Let `tys` be an `ArchTypeFamily` for $F$: a number $\mathrm{card}(w)$ for each infinite place $w$ together with, for each $i < \mathrm{card}(w)$, an `ArchRepAt F w`, that is a natural number $n$ and a representation $\rho$ of `rowIsometrySubgroup₀ w.Completion` on $\mathbb C^n$. Let $x : GL_2(\mathbb A_F) \to \mathbb C$ be continuous and lie in $\mathrm{archCutSubmodule}\,F\,\mathrm{tys} = \bigsqcap_{w \mid \infty} \bigsqcup_{i < \mathrm{card}(w)} \mathrm{archTypeSubmoduleAt}\,F\,w\,(\mathrm{tys.rep}\,w\,i)$, the infimum over infinite places of the suprema of the submodules `typeSubmodule` attached to the inclusion `rowIsometryInclAt₀ F w` and the representation of the corresponding type. Write $E$ for the $\mathbb C$-span of the set of functions $g \mapsto x(g \cdot \mathrm{adelicArchGLIncl}\,F\,(\iota\kappa))$, $\kappa \in \mathcal K$, where `adelicArchGLIncl` embeds $GL_2(\mathbb A_{F,\infty})$ into $GL_2(\mathbb A_F)$ through the product decomposition of the adelic matrix ring, with finite component $1$. The conclusion is fourfold: $E$ is finite-dimensional over $\mathbb C$; every element of $E$ is continuous; $E$ is contained in $\mathrm{archCutSubmodule}\,F\,\mathrm{tys}$; and for every $v \in E$ and every $\kappa \in \mathcal K$ the right translate $g \mapsto v(g \cdot \mathrm{adelicArchGLIncl}\,F\,(\iota\kappa))$ again lies in $E$.
--
--   This is the joint-places form of Harish-Chandra's finiteness for $K$-finite vectors: a continuous function whose archimedean behaviour is cut out by finitely many types at each infinite place generates, under right translation by the full product of the archimedean compact groups, a finite-dimensional translation-stable space of continuous functions still inside the type cut. It reduces place by place to the single-place statement [`AutomorphicForm.CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt`](thm.html#AutomorphicForm.CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt), and supplies the finite-dimensional stable space used in the construction of the archimedean type projector and in the approximation arguments for the cuspidal spectrum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_finiteDimensional_span_translates_of_mem_archCutSubmodule.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.finiteDimensional_span_translates_of_mem_archCutSubmodule
    (F : Type) [Field F] [NumberField F]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (tys : AutomorphicForm.ArchTypeFamily F)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hxc : Continuous x) (hxt : x ∈ archCutSubmodule F tys) :
    FiniteDimensional ℂ ↥(Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ)))) ∧
    (∀ v ∈ Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ))), Continuous v) ∧
    Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ))) ≤ archCutSubmodule F tys ∧
    ∀ v ∈ Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ))), ∀ κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
      (fun g : AdelicGL2 (𝓞 F) F => v (g * adelicArchGLIncl F (ι κ))) ∈ Submodule.span ℂ (Set.range fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => fun g : AdelicGL2 (𝓞 F) F => x (g * adelicArchGLIncl F (ι κ))) := by sorry
