-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous
-- name    : AutomorphicForm.CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/20665093-0738-513e-b3ca-e29a1a4a4ca3
-- title:
--   Archimedean type splitting for stable spaces of continuous functions
-- statement:
--   Let $F$ be a number field, $w$ an infinite place of $F$, and let $K$ denote the group `rowIsometrySubgroup₀ w.Completion`, a subgroup of $\mathrm{GL}_2(F_w)$, acting on functions $\mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ through its embedding `rowIsometryInclAt₀ F w` into $\mathrm{GL}_2(\mathbb{A}_F)$ by right translation, $(\mathrm{rightTranslate}\,g\,\varphi)(x) = \varphi(xg)$. Let $\rho_0,\dots,\rho_{m-1}$ and $\sigma_0,\dots,\sigma_{r-1}$ be families of archimedean representation data at $w$, each consisting of a dimension $n$ together with a representation of $K$ on $\mathbb{C}^n$, and for such a datum $\tau$ let $\mathcal{T}_w(\tau)$ be the $\mathbb{C}$-span of all functions lying in the range of a linear map from the representation space into functions on $\mathrm{GL}_2(\mathbb{A}_F)$ that is right equivariant for the representation. Assume that every finite-dimensional, nonzero, $K$-stable $\mathbb{C}$-submodule $S$ of functions on $\mathrm{GL}_2(\mathbb{A}_F)$ which is simple (every $K$-stable $S' \le S$ is $\bot$ or $S$) and satisfies $S \le \bigvee_i \mathcal{T}_w(\rho_i)$ is contained in $\mathcal{T}_w(\sigma_j)$ for some $j$. Let $Q$ be a $\mathbb{C}$-submodule all of whose members are continuous and which is stable under right translation by $K$. Then $Q \cap \bigvee_i \mathcal{T}_w(\rho_i) \le \bigvee_j \bigl(Q \cap \mathcal{T}_w(\sigma_j)\bigr)$.
--
--   This is the one-place form of Weyl's unitarian trick in the present setting: the $K$-span of a member of the left-hand side is finite-dimensional and consists of continuous functions, hence decomposes into simple $K$-submodules, which by hypothesis lie in the types $\mathcal{T}_w(\sigma_j)$. It is used by the lemmas that split an archimedean cut of a cuspidal subrepresentation into irreducible archimedean types, and cites the finiteness of such $K$-spans, complete reducibility for continuous finite-dimensional representations of a compact group, and the compactness of the row-isometry subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous.lean

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

theorem AutomorphicForm.CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)
    (m : ℕ) (ρs : Fin m → ArchRepAt F w) (r : ℕ) (σs : Fin r → ArchRepAt F w)
    (hσ : ∀ S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), FiniteDimensional ℂ ↥S →
        (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S) →
        S ≠ ⊥ →
        (∀ S' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), S' ≤ S →
          (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S', rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S') →
          S' = ⊥ ∨ S' = S) →
        S ≤ ⨆ i, archTypeSubmoduleAt F w (ρs i) →
        ∃ j, S ≤ archTypeSubmoduleAt F w (σs j))
    (Q : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hQc : ∀ g ∈ Q, Continuous g)
    (hQs : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ Q, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ Q) :
    Q ⊓ (⨆ i, archTypeSubmoduleAt F w (ρs i)) ≤ ⨆ j, Q ⊓ archTypeSubmoduleAt F w (σs j) := by sorry
