-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_exists_submodule_maximalCompact_finrank_le_restrict_mem_of_isInducedSection_principalLevel_archCutSubmodule
-- name    : AutomorphicForm.exists_forall_exists_submodule_maximalCompact_finrank_le_restrict_mem_of_isInducedSection_principalLevel_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/40772fca-c1e1-5e5c-9ca0-dd051e3add7f
-- title:
--   Uniform dimension bound for induced sections restricted to K
-- statement:
--   Let $K$ be a number field, $N$ a nonzero ideal of $\mathcal O_K$, and $\mathrm{tysK}$ an archimedean type family on $K$, that is, a number $\mathrm{card}(w)$ of archimedean representations $\mathrm{rep}(w,i)$ attached to each infinite place $w$. Write $\alpha_m$ for the real character of the idele units obtained from the distributive Haar character of $\mathbb A_K$ composed with $\mathbb R_{\ge 0}\to\mathbb R$, passed to units. The assertion is the existence of a single $D\in\mathbb N$, depending only on $K$, $N$ and $\mathrm{tysK}$, such that for every proof that $\alpha_m$ takes positive values, every pair of characters $\mu,\nu\colon\mathbb A_K^\times\to\mathbb C^\times$ that are unitary ($|\mu(x)|=|\nu(x)|=1$ for all $x$), trivial on the principal ideles coming from $K^\times$, and continuous, every $s\in\mathbb C$, and every $\varphi\colon \mathrm{GL}_2(\mathbb A_K)\to\mathbb C$ satisfying: (i) $\varphi(bg)=\eta_1(d_1(b))\,\eta_2(d_2(b))\,\varphi(g)$ for all $b$ in the adelic Borel subgroup and all $g$, where $\eta_1=\mu\cdot\alpha_m^{s+1/2}$ and $\eta_2=\nu\cdot\alpha_m^{-(s+1/2)}$ and $d_1,d_2$ are the two diagonal characters of the Borel; (ii) $\varphi$ continuous; (iii) $\varphi(gu)=\varphi(g)$ for all $g$ and all $u$ in the intersection of the principal level subgroup of level $N$ with the kernel of the archimedean projection; (iv) for each infinite place $w$ a finite-dimensional $\mathbb C$-subspace $W$ of functions on the subgroup $\mathrm{archRowIsometrySubgroup}(K,w)$ (the image of the row-isometry subgroup of $\mathrm{GL}_2(K_w)$) containing $k\mapsto\varphi(gk)$ for every $g$; and (v) $\varphi$ in $\mathrm{archCutSubmodule}$, the infimum over infinite places $w$ of the supremum over $i<\mathrm{card}(w)$ of the type submodules attached to $\mathrm{rep}(w,i)$; there exists a $\mathbb C$-submodule $V$ of functions on the maximal compact $\mathbf K=\mathrm{adelicMaximalCompact}(K)$ (elements whose finite part is integral and whose archimedean components are row isometries) such that $V$ is finite-dimensional with $\operatorname{finrank}_{\mathbb C}V\le D$, every member of $V$ is continuous, $V$ is stable under right translation by elements of $\mathbf K$, and the restriction $k\mapsto\varphi(k)$ of $\varphi$ to $\mathbf K$ lies in $V$.
--
--   This is the $\mathbf K$-finiteness statement for induced (principal-series) sections of level $N$ and prescribed archimedean types, with a dimension bound uniform in the inducing characters and in the complex parameter $s$; the bound is inherited from the corresponding uniform bound on orthonormal families. It feeds the uniform sup-norm and intertwining estimates on the maximal compact used in the analytic part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_exists_submodule_maximalCompact_finrank_le_restrict_mem_of_isInducedSection_principalLevel_archCutSubmodule.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm

theorem AutomorphicForm.exists_forall_exists_submodule_maximalCompact_finrank_le_restrict_mem_of_isInducedSection_principalLevel_archCutSubmodule
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tysK : ArchTypeFamily K) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ D : ℕ, ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (s : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) φ)
      (_hφc : Continuous φ)
      (_hφlev : ∀ (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ (g * u) = φ g)
      (_hφKu : ∀ w : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ g : AdelicGL2 (𝓞 K) K,
          (fun k : ↥(archRowIsometrySubgroup K w) => φ (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφty : φ ∈ archCutSubmodule K tysK),
      ∃ V : Submodule ℂ (↥(adelicMaximalCompact K) → ℂ),
        FiniteDimensional ℂ ↥V ∧ Module.finrank ℂ ↥V ≤ D ∧
        (∀ f ∈ V, Continuous f) ∧
        (∀ f ∈ V, ∀ k : ↥(adelicMaximalCompact K), (fun x : ↥(adelicMaximalCompact K) => f (x * k)) ∈ V) ∧
        (fun k : ↥(adelicMaximalCompact K) => φ (k : AdelicGL2 (𝓞 K) K)) ∈ V := by sorry
