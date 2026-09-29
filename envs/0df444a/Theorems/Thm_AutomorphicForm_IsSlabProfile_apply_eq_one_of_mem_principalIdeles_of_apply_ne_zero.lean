-- Prove2me | Theorems.Thm_AutomorphicForm_IsSlabProfile_apply_eq_one_of_mem_principalIdeles_of_apply_ne_zero
-- name    : AutomorphicForm.IsSlabProfile.apply_eq_one_of_mem_principalIdeles_of_apply_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/b9017347-2022-53a3-89a2-9e783c2bfc28
-- title:
--   Triviality of a slab profile's central character on principal ideles
-- statement:
--   Let $F$ be a number field with ring of integers $\mathcal{O}_F$, let $Z$ be a subgroup of the idele group $(\mathbb{A}_F)^\times$ of units of the adele ring, let $\xi\colon Z \to \mathbb{C}^\times$ be a group homomorphism, and let $\varphi\colon \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a function satisfying [`AutomorphicForm.IsSlabProfile F Z ξ φ`](def/AutomorphicForm_SlabProfile.html#L17), i.e. $\varphi$ is measurable, invariant under left multiplication by the adelic unipotent matrices $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, invariant under left multiplication by the image in $\mathrm{GL}_2(\mathbb{A}_F)$ of any $\gamma \in \mathrm{GL}_2(F)$ whose $(1,0)$ entry vanishes, transforms by $\varphi(\mathrm{diag}(z,z)g) = \xi(z)\varphi(g)$ for $z \in Z$, is bounded on each slab where the idele norm of $\det g$ lies in an interval $[d_1,d_2]$ with $d_1>0$, and has its non-vanishing locus contained in a band $a \le \mathrm{adelicHeight}_F(g) \le b$ with $a>0$. Assume there exists $g_0$ with $\varphi(g_0) \neq 0$. Then for every $z \in Z$ whose underlying idele lies in [`M4aHerbrand.principalIdeles`](def/M4aHerbrand_IdeleClassVocab.html#L16), that is, in the image of $F^\times$ under the diagonal embedding into $(\mathbb{A}_F)^\times$, one has $\xi(z) = 1$.
--
--   This is the standard compatibility constraint on the central character of a non-zero automorphic-type function that is left invariant under the rational Borel subgroup: such a character must be trivial on $Z \cap F^\times$. It supplies that triviality hypothesis to the later averaging/approximation step for slab profiles, [`AutomorphicForm.exists_isSlabProfile_paleyWiener_eLpNorm_sub_restrict_rationalTorusUnipotentQuotient_lt_of_isSlabProfile`](thm.html#AutomorphicForm.exists_isSlabProfile_paleyWiener_eLpNorm_sub_restrict_rationalTorusUnipotentQuotient_lt_of_isSlabProfile).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_IsSlabProfile_apply_eq_one_of_mem_principalIdeles_of_apply_ne_zero.lean

import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_CarrierPins
import Mathlib.Analysis.Meromorphic.NormalForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

theorem AutomorphicForm.IsSlabProfile.apply_eq_one_of_mem_principalIdeles_of_apply_ne_zero
    (F : Type) [Field F] [NumberField F]
    (Z : Subgroup (AdeleRing (𝓞 F) F)ˣ) (ξ : Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (_hφ : AutomorphicForm.IsSlabProfile F Z ξ φ)
    (g₀ : AdelicGL2 (𝓞 F) F) (_hg₀ : φ g₀ ≠ 0)
    (z : Z) (_hz : (z : (AdeleRing (𝓞 F) F)ˣ) ∈ M4aHerbrand.principalIdeles (𝓞 F) F) :
    ξ z = 1 := by sorry
