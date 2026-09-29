-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt
-- name    : AutomorphicForm.CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/348d37d0-f6a7-5c40-921d-9742a441a264
-- title:
--   Finite-dimensional K-span of vectors in finitely many archimedean types
-- statement:
--   Let $F$ be a number field, $w$ an infinite place of $F$, and write $G = \mathrm{GL}_2(\mathbb{A}_F)$ for `AdelicGL2 (𝓞 F) F`, the general linear group of degree $2$ over the adele ring of $F$. Let $m$ be a natural number and let $\rho_0,\dots,\rho_{m-1}$ be given by a family $\rho s : \mathrm{Fin}\ m \to$ `ArchRepAt F w`, so each $\rho s_i$ consists of a dimension $n_i$ together with a complex representation of the group `rowIsometrySubgroup₀ w.Completion` on $\mathbb{C}^{n_i}$. For $\tau$ such a datum, `archTypeSubmoduleAt F w τ` is the span of all functions $G \to \mathbb{C}$ lying in the range of some $\mathbb{C}$-linear map $T : \mathbb{C}^{n} \to (G \to \mathbb{C})$ that is right equivariant, in the sense of `IsRightEquivariant`, for the monoid homomorphism `rowIsometryInclAt₀ F w` into $G$ and the representation $\tau.\rho$. Assume $\varphi : G \to \mathbb{C}$ belongs to the supremum $\bigsqcup_i$ `archTypeSubmoduleAt F w (ρs i)`. Let $S$ be the $\mathbb{C}$-span of the set of right translates $x \mapsto \varphi(x \cdot$ `rowIsometryInclAt₀ F w k`$)$, as $k$ ranges over `rowIsometrySubgroup₀ w.Completion`. Then $S$ is finite-dimensional over $\mathbb{C}$, $S$ is stable under right translation by `rowIsometryInclAt₀ F w k` for every such $k$, and $S$ is contained in the same supremum of archimedean type subspaces.
--
--   This is the statement that a vector lying in a sum of finitely many archimedean $K$-types is $K$-finite, with the span of its translates again contained in that sum. It is used when decomposing cuspidal cut spaces into irreducible archimedean types one infinite place at a time, and is cited by the results on highest-weight decompositions at complex places and on the interaction of cuts with suprema of type subspaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)
    (m : ℕ) (ρs : Fin m → ArchRepAt F w)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ ⨆ i, archTypeSubmoduleAt F w (ρs i)) :
    let S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
      Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ w.Completion =>
        rightTranslate F (rowIsometryInclAt₀ F w k) φ)
    FiniteDimensional ℂ ↥S ∧
      (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S) ∧
      S ≤ ⨆ i, archTypeSubmoduleAt F w (ρs i) := by sorry
