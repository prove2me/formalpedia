-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_add_smul_reflect_lower_mem_and_isIsotypicCuspFormAt_of_mem_isCuspConstituent
-- name    : AutomorphicForm.CuspidalConstituent.add_smul_reflect_lower_mem_and_isIsotypicCuspFormAt_of_mem_isCuspConstituent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/7e02827b-472d-51d0-b739-83e2554bf934
-- title:
--   Stability of weight-one isotypic vectors under reflected lowering
-- statement:
--   Work over $\mathbb{Q}$ at the pins `productionPinsGeneral ℚ`. Let $\xi$ be a homomorphism from the central subgroup $Z$ of these pins to $\mathbb{C}^\times$, let $N$ be a nonzero ideal of $\mathcal{O}_{\mathbb{Q}}$, $S$ a finite set of height-one primes, and $\Phi$ a Hecke eigensystem over $\mathbb{Q}$ with complex coefficients (a nonzero level together with families $a_v$, $b_v$). Let $V$ be a $\mathbb{C}$-submodule of the functions $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}}) \to \mathbb{C}$ which is a cuspidal constituent for $\xi$: it is a cuspidal subrepresentation in the sense of `IsCuspSubrep`, it is nonzero, and any cuspidal subrepresentation contained in it is either $0$ or all of $V$. Let $\varphi \in V$ satisfy `IsIsotypicCuspFormAt` for $(\xi, N, S, \Phi)$, i.e. $\varphi$ is a smooth cuspidal automorphic function for $(\xi)$, continuous, right invariant under the level subgroup $\mathrm{U}(N)$ of the pins, a Hecke coset eigenfunction with eigenvalue $\Phi.a\,v$ at every $v \notin S$, and satisfies the central eigenvalue relation with $\Phi$'s raw central datum $b_v$ for $v \notin S$. Let $w$ be a real infinite place of $\mathbb{Q}$ and $\lambda \in \mathbb{C}$, and assume: $\varphi$ satisfies `HasArchCharacterAt₀` for the character `archWeightCharAt hw 1`, the first power of `archWeightOneAt hw` on the subgroup `rowIsometrySubgroup₀` at $w$ (weight one at $w$); $\varphi$ is archimedean smooth at $w$, meaning that for every $g$ the function $e \mapsto \varphi(g \cdot \mathrm{archRealLiftAt}\,e)$ is $C^\infty$ on the set of real $2\times 2$ matrices of nonzero determinant; and $\mathrm{archCasimirAt}\,\varphi = \lambda\varphi$, where the Casimir operator is $-\bigl(\tfrac14 D_H^2 - \tfrac12 D_H + D_E D_{F^-}\bigr)$ with $D_d$ the derivative at $t = 0$ along the one-parameter flow in direction $d$ embedded at $w$. Then for every $c \in \mathbb{C}$ the function $$\psi := \varphi + c\,\bigl(g \mapsto \bigl(D_H\varphi - i\,(D_E\varphi + D_{F^-}\varphi)\bigr)(g \cdot \mathrm{archRealGLAt}\,J)\bigr),$$ with $J$ the matrix `UpperHalfPlane.J` embedded at $w$, lies in $V$, satisfies `IsIsotypicCuspFormAt` for the same data $(\xi, N, S, \Phi)$, has the same weight-one transformation law at $w$, is archimedean smooth at $w$, satisfies $\mathrm{archCasimirAt}\,\psi = \lambda\psi$, and has $D_d\psi$ continuous for each of the three directions $d \in \{H, E, F^-\}$.
--
--   This is the stability statement for the weight-one slice of a cuspidal constituent under the reflected lowering operator $T\varphi = \bigl((D_H - i(D_E + D_{F^-}))\varphi\bigr)(\,\cdot\,J)$: adding any multiple of $T\varphi$ to a weight-one Hecke-isotypic vector of $V$ preserves membership in $V$, the isotypic conditions, the weight, smoothness and the Casimir eigenvalue, and yields continuous first flow derivatives. It is used in the Langlands–Tunnell converse construction to produce, from a given weight-one vector, a vector in the same constituent with prescribed behaviour of its Whittaker coefficients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_add_smul_reflect_lower_mem_and_isIsotypicCuspFormAt_of_mem_isCuspConstituent.lean

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

theorem AutomorphicForm.CuspidalConstituent.add_smul_reflect_lower_mem_and_isIsotypicCuspFormAt_of_mem_isCuspConstituent
    (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ) (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (Φ : HeckeEigensystem ℚ ℂ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 ℚ) ℚ → ℂ))
    (hV : CuspidalConstituent.IsCuspConstituent ℚ (productionPinsGeneral ℚ) ξ V)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφV : φ ∈ V)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ φ)
    (w : InfinitePlace ℚ) (hw : w.IsReal) (lam : ℂ)
    (hwt : HasArchCharacterAt₀ ℚ w (archWeightCharAt hw 1) φ)
    (hsm : IsArchSmoothAt hw φ) (hcas : archCasimirAt hw φ = lam • φ)
    (c : ℂ) :
    let ψ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := φ + c • (fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
      (archDerivAt hw ArchDir.H φ - Complex.I • (archDerivAt hw ArchDir.E φ + archDerivAt hw ArchDir.Fm φ))
        (g * archRealGLAt hw UpperHalfPlane.J))
    ψ ∈ V ∧
    IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ N S Φ ψ ∧
    HasArchCharacterAt₀ ℚ w (archWeightCharAt hw 1) ψ ∧
    IsArchSmoothAt hw ψ ∧ archCasimirAt hw ψ = lam • ψ ∧
    (∀ d : ArchDir, Continuous (archDerivAt hw d ψ)) := by sorry
