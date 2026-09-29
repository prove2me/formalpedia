-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isInducedSection_continuous_forall_maximalCompact_eq_of_equivariant_kFinite
-- name    : AutomorphicForm.exists_isInducedSection_continuous_forall_maximalCompact_eq_of_equivariant_kFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/31502ebb-5812-5f3d-8e0a-edfcb7a22bde
-- title:
--   Iwasawa extension of an equivariant K-finite function to an induced section
-- statement:
--   Let $F$ be a number field, and let $\alpha \colon (\mathbb A_F)^\times \to \mathbb R^\times$ be the character obtained from the distributive Haar character `distribHaarChar (AdeleRing (𝓞 F) F)` by pushing its $\mathbb R_{\ge 0}$-values into $\mathbb R$ and passing to units; assume $\alpha$ takes positive values. Let $\mu,\nu \colon (\mathbb A_F)^\times \to \mathbb C^\times$ be homomorphisms whose $\mathbb C$-valued coordinate functions are continuous, let $s \in \mathbb C$, and write $\eta_1 = \mu\cdot\alpha^{s+1/2}$ (`etaFst`) and $\eta_2 = \nu\cdot\alpha^{-(s+1/2)}$ (`etaSnd`), the complex powers being formed from the positive reals $\alpha(x)$. Let $\mathbf K =$ `adelicMaximalCompact F` be the subgroup of $g \in GL_2(\mathbb A_F)$ whose finite part lies in `finiteIntegralGL2` and whose component at every infinite place $w$ satisfies `IsRowIsometry` (unit determinant norm, and the two rows act isometrically on pairs of scalars). Let $u \colon \mathbf K \to \mathbb C$ be continuous and assume: all right translates $k \mapsto u(kk_0)$, $k_0 \in \mathbf K$, lie in a single finite-dimensional $\mathbb C$-subspace of functions on $\mathbf K$; there is a neighbourhood $V$ of $1$ in $GL_2(\mathbb A_F)$ such that $u(ku') = u(k)$ for all $k \in \mathbf K$ and all $u' \in \mathbf K \cap V$ with trivial archimedean component, i.e. $u' \in \ker(\mathrm{gl}_\mathrm{arch})$; and $u(bk) = \eta_1(b_{00})\,\eta_2(b_{11})\,u(k)$ whenever $b$ lies in $\mathbf K$ and in the Borel subgroup (lower left entry zero) and $k \in \mathbf K$. Then there exists $\varphi_0 \colon GL_2(\mathbb A_F) \to \mathbb C$ such that $\varphi_0(bg) = \eta_1(b_{00})\,\eta_2(b_{11})\,\varphi_0(g)$ for every $b$ in the Borel subgroup and every $g$ (`IsInducedSection`); `IsArchKFinite F φ₀`, that is, at every infinite place $w$ the predicate `RightTranslatesSpanFinite` holds for $\varphi_0$ with respect to `archRowIsometrySubgroup F w`; `IsKfSmooth F φ₀`, that is, the stabiliser of $\varphi_0$ for right translation inside $\ker(\mathrm{gl}_\mathrm{arch})$ is open; $\varphi_0$ is continuous; and $\varphi_0(k) = u(k)$ for all $k \in \mathbf K$.
--
--   This is the Iwasawa-decomposition extension step for the adelic principal series: a $\mathbf K$-datum which is finite, smooth at the finite places and equivariant for the character $\eta_s$ on $B(\mathbb A_F)\cap\mathbf K$ extends uniquely to a section of the induced representation $I(\mu,\nu,s)$, with the prescribed restriction to $\mathbf K$. It supplies the free $\mathbf K$-datum used by [`AutomorphicForm.exists_isInducedSection_eLpNorm_sub_sum_mul_restrict_maximalCompact_le_of_isSlabProfile`](thm.html#AutomorphicForm.exists_isInducedSection_eLpNorm_sub_sum_mul_restrict_maximalCompact_le_of_isSlabProfile) in the approximation of slab profiles.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isInducedSection_continuous_forall_maximalCompact_eq_of_equivariant_kFinite.lean

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

theorem AutomorphicForm.exists_isInducedSection_continuous_forall_maximalCompact_eq_of_equivariant_kFinite
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (s : ℂ)
      (u : ↥(adelicMaximalCompact F) → ℂ) (_huc : Continuous u)
      (_huW : ∃ W : Submodule ℂ (↥(adelicMaximalCompact F) → ℂ), FiniteDimensional ℂ W ∧
        ∀ k₀ : ↥(adelicMaximalCompact F), (fun k => u (k * k₀)) ∈ W)
      (_husm : ∃ V ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F), ∀ (k u' : ↥(adelicMaximalCompact F)),
        (u' : AdelicGL2 (𝓞 F) F) ∈ V → (u' : AdelicGL2 (𝓞 F) F) ∈ finiteAdelicGL2Subgroup F →
          u (k * u') = u k)
      (_hueq : ∀ (b : AdelicGL2 (𝓞 F) F) (hb : b ∈ adelicBorel (𝓞 F) F) (hbK : b ∈ adelicMaximalCompact F)
        (k : ↥(adelicMaximalCompact F)),
        u (⟨b, hbK⟩ * k) =
          ((etaFst μ α hα s (borelDiagFst ⟨b, hb⟩) : ℂˣ) : ℂ) * ((etaSnd ν α hα s (borelDiagSnd ⟨b, hb⟩) : ℂˣ) : ℂ) *
            u k),
    ∃ φ₀ : AdelicGL2 (𝓞 F) F → ℂ,
      IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ₀ ∧
      IsArchKFinite F φ₀ ∧ IsKfSmooth F φ₀ ∧ Continuous φ₀ ∧
      ∀ k : ↥(adelicMaximalCompact F), φ₀ (k : AdelicGL2 (𝓞 F) F) = u k := by sorry
