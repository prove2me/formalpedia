-- Prove2me | Theorems.Thm_AutomorphicForm_table_mem_box_of_mem_cuspClasses_siegel
-- name    : AutomorphicForm.table_mem_box_of_mem_cuspClasses_siegel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/af885966-2ca0-58bd-9b58-9fc78340600b
-- title:
--   Satake table of a principal-level cuspidal class lies in a box
-- statement:
--   Let $K$ be a number field, let $c_K,u_K,d_{1,K},d_{2,K}$ be real numbers with $c_K>0$ and $0<d_{1,K}<d_{2,K}$, and let $T_K$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Write $D$ for the union over $x\in T_K$ of the right translates by $x$ of the centre-cut Siegel set $\mathrm{centreCutSiegelSet}\,K\,c_K\,u_K\,d_{1,K}\,d_{2,K}$, namely the set of adelic $g$ whose finite part lies in the integral subgroup, whose archimedean component at every infinite place $w$ has local height at least $c_K$ and squared $x$-window at most $u_K^2$, and whose archimedean determinant norm at every $w$ lies in $[d_{1,K},d_{2,K}]$; assume $D$ covers modulo the centre, i.e. every $g\in\mathrm{GL}_2(\mathbb{A}_K)$ satisfies $\gamma g z\in D$ for some $\gamma\in\mathrm{GL}_2(K)$ (via global points) and some central scalar $z$ with $z\in\mathbb{A}_K^\times$. Let $\xi_K$ be a homomorphism from the full subgroup $\top$ of $\mathbb{A}_K^\times$ to $\mathbb{C}^\times$ which is continuous as a $\mathbb{C}$-valued function and trivial on the image of $K^\times$. Let $S_K$ be a finite set of finite places of $K$ and $N'$ an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$. Let $\pi$ be a Hecke eigensystem over $\mathbb{C}$ for $K$ (a nonzero level ideal together with families $a,b$ indexed by the finite places) belonging to $\mathrm{cuspClasses}$ for the carrier data $\mathrm{productionPinsOf}$ built from $D$, the level family $M\mapsto \mathrm{principalLevel}(M)\sqcap\ker(\mathrm{glArch})$, the generators $v\mapsto \mathrm{heckeGen}_v$ and the adelic box (Borel structures, the adelic $\mathrm{GL}_2$ Haar measure, $Z=\top$ and the Haar measure on the adeles conditioned on the box), with character $\xi_K$, level $N'$ and set $S_K$; that is, $\pi$ has level $N'$, satisfies $a_v=b_v=0$ for all $v\in S_K$, and has nonvanishing isotypic cusp submodule. The conclusion is that the table $v\mapsto(a_v,b_v)$ lies in the set of functions $x$ into $\mathbb{C}\times\mathbb{C}$ such that $x_v=0$ for $v\in S_K$, and for every $v\notin S_K$, writing $\varpi_v=\det(\mathrm{heckeGen}_v)$: the second coordinate equals $\mathrm{N}(v)\,\xi_K(\varpi_v)$ with $\mathrm{N}(v)$ the absolute norm of $v$ viewed in $\mathbb{C}$; the first coordinate has norm at most $(\mathrm{N}(v)+1)\sqrt{\lVert\xi_K(\varpi_v)\rVert}$; and $\overline{(x_v)_1}=\bigl(\overline{(x_v)_2}/\lVert (x_v)_2\rVert\bigr)(x_v)_1$.
--
--   This records that the Satake parameters of a cuspidal Hecke eigensystem of principal level, realised against a Siegel-set cover of $\mathrm{GL}_2(\mathbb{A}_K)$ modulo the centre, satisfy the central-character identity for $b_v$, the trivial bound on $a_v$, and the Hermitian normalisation relating $a_v$ and $b_v$, so that the table lies in a fixed compact box. It is the input to the comparison of fibre sums of twisted and untwisted cut traces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_table_mem_box_of_mem_cuspClasses_siegel.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_LocalLanglands_IntegralSubgroupOpen
import Definitions.Def_LocalLanglands_HeckePair
import Definitions.Def_DedekindDomain_IntegralClosure
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_HeckeEigenfunction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain MeasureTheory NumberField.AdelicHaar AutomorphicForm NumberField.TateGlobal AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering LocalGL2
open scoped TensorProduct Pointwise TensorProduct.RightActions ComplexConjugate BigOperators NumberField NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.table_mem_box_of_mem_cuspClasses_siegel
    (K : Type) [Field K] [NumberField K]
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (N' : Ideal (𝓞 K)) (hN' : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N' → v ∈ SK)
    (π : HeckeEigensystem K ℂ)
    (hπ : π ∈ cuspClasses K
      (productionPinsOf K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K)
          (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K)
          (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) ξK N' SK) :
    (fun v : HeightOneSpectrum (𝓞 K) => (π.a v, π.b v)) ∈
      {x : HeightOneSpectrum (𝓞 K) → ℂ × ℂ |
        (∀ v ∈ SK, x v = 0) ∧
        ∀ v ∉ SK,
          (x v).2 = HeckeEigensystem.cNorm v *
              ((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x v).1‖ ≤ ((Ideal.absNorm v.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξK ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x v).1 = conj (x v).2 / ((‖(x v).2‖ : ℝ) : ℂ) * (x v).1} := by sorry
