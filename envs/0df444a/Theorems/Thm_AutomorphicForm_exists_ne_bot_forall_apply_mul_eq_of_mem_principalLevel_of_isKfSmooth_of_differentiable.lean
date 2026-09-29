-- Prove2me | Theorems.Thm_AutomorphicForm_exists_ne_bot_forall_apply_mul_eq_of_mem_principalLevel_of_isKfSmooth_of_differentiable
-- name    : AutomorphicForm.exists_ne_bot_forall_apply_mul_eq_of_mem_principalLevel_of_isKfSmooth_of_differentiable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/9c6a1608-fd7b-5fc7-9c33-7a4c790ce2aa
-- title:
--   A common principal level for a holomorphic K_f-smooth family
-- statement:
--   Let $K$ be a number field, and let $\psi$ assign to each $s \in \mathbb{C}$ a complex-valued function on $\mathrm{GL}_2$ of the adele ring of $K$ (the group `AdelicGL2 (𝓞 K) K`). Assume first that for every $s$ the function $\psi_s$ is $K_f$-smooth, i.e. its stabiliser for the right-translation action of the subgroup `finiteAdelicGL2Subgroup K` — the kernel of the map $\mathrm{GL}_2(\mathbb{A}_K) \to \mathrm{GL}_2(\mathbb{A}_{K,\infty})$ induced by the projection of the adeles onto the infinite adeles — is an open subset of that subgroup; assume second that for each fixed $g$ the function $s \mapsto \psi_s(g)$ is differentiable on all of $\mathbb{C}$, hence entire. The conclusion is that a single level works for the whole family: there is a nonzero ideal $N'$ of $\mathcal{O}_K$ such that for every $s \in \mathbb{C}$, every $g \in \mathrm{GL}_2(\mathbb{A}_K)$ and every $u$ lying in the intersection of `principalLevel (𝓞 K) K N'` — the meet of the level-one subgroup `levelOne` at $N'$ with its conjugate by the Weyl element $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ — with `finiteAdelicGL2Subgroup K`, one has $\psi_s(gu) = \psi_s(g)$.
--
--   This uniformises the level of a family of automorphic functions depending holomorphically on a complex parameter: individual $K_f$-smoothness gives each member an open stabiliser, but a priori no level is common to all $s$. It supplies the level hypothesis in the Paley–Wiener/Weyl-intertwining computations of the project, being cited by the three statements about the axis pairing and its Weyl intertwining for matched Paley–Wiener data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_ne_bot_forall_apply_mul_eq_of_mem_principalLevel_of_isKfSmooth_of_differentiable.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_ne_bot_forall_apply_mul_eq_of_mem_principalLevel_of_isKfSmooth_of_differentiable
    (K : Type) [Field K] [NumberField K]
    (ψ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
    (_hψsm : ∀ s, IsKfSmooth K (ψ s))
    (_hψhol : ∀ g : AdelicGL2 (𝓞 K) K, Differentiable ℂ (fun s => ψ s g)) :
    ∃ N' : Ideal (𝓞 K), N' ≠ ⊥ ∧
      ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N' ⊓ finiteAdelicGL2Subgroup K, ψ s (g * u) = ψ s g := by sorry
