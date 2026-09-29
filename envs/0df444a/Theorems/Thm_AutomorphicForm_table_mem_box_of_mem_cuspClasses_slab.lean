-- Prove2me | Theorems.Thm_AutomorphicForm_table_mem_box_of_mem_cuspClasses_slab
-- name    : AutomorphicForm.table_mem_box_of_mem_cuspClasses_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/0178e882-8da9-5701-ab26-1b5b4cd09207
-- title:
--   Hecke tables of cuspidal slab classes lie in the box
-- statement:
--   Let $L$ be a number field, let $0<\alpha<\beta$ be reals, and let $\Phi_L$ be a subset of $\mathrm{GL}_2(\mathbb{A}_L)$ contained in the slab $\{g : \|\det g\| \in [\alpha,\beta]\}$, where $\|\cdot\|$ is the idèle norm [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), i.e. the module of multiplication on the adèle ring; assume $\Phi_L$ is a fundamental domain for the image of $\mathrm{GL}_2(L)$ under `globalPoints` with respect to the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_L)$ restricted to that slab. Let $\xi_L$ be a homomorphism from the full subgroup of idèle units to $\mathbb{C}^\times$ that is continuous and trivial on principal idèles, let $S_L$ be a finite set of finite places of $L$, and let $N$ be an ideal of $\mathcal{O}_L$ all of whose prime divisors lie in $S_L$. Let $\Psi$ be a Hecke eigensystem over $\mathbb{C}$ (a nonzero level ideal together with coefficient functions $a,b$ on finite places) lying in `cuspClasses` for the carrier assembled from $\Phi_L$, the centre $\top$, the level groups $M \mapsto \mathrm{levelOne}(M) \sqcap \mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators $g_w = \mathrm{heckeGen}(w)$ and the adelic box: that is, $\Psi$ has level $N$, $a$ and $b$ vanish on $S_L$, and the span of the associated isotypic cusp forms is nonzero. Then $w \mapsto (\Psi.a\,w, \Psi.b\,w)$ vanishes on $S_L$ and satisfies, for every $w \notin S_L$, writing $\chi_w = \xi_L(\det g_w)$ and $N(w) = \mathrm{absNorm}(w)$: $\Psi.b\,w = N(w)\,\chi_w$, $\|\Psi.a\,w\| \le (N(w)+1)\sqrt{\|\chi_w\|}$, and $\overline{\Psi.a\,w} = \bigl(\overline{\Psi.b\,w}/\|\Psi.b\,w\|\bigr)\,\Psi.a\,w$.
--
--   The three clauses record, for a cuspidal class attached to the slab carrier, the action of the central element at $w$ through $\xi_L$, the trivial bound for the Hecke operator at $w$ as a sum of $N(w)+1$ translates, and the Hermitian normalisation of that operator for the weighted pairing on the slab. The statement places the Hecke table of such a class inside an explicitly described box of coefficient functions, and is used in the comparison of twisted and untwisted fibre sums of cut traces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_table_mem_box_of_mem_cuspClasses_slab.lean

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

open NumberField NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain MeasureTheory NumberField.AdelicHaar NumberField.TateGlobal AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering LocalGL2
open AutomorphicForm
open scoped TensorProduct Pointwise TensorProduct.RightActions ComplexConjugate BigOperators NumberField NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.table_mem_box_of_mem_cuspClasses_slab
    (L : Type) [Field L] [NumberField L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξL ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξL ⟨z, Subgroup.mem_top z⟩ = 1)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (Ψ : HeckeEigensystem L ℂ)
    (hΨ : Ψ ∈ cuspClasses L
      (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL N SL) :
    (fun w : HeightOneSpectrum (𝓞 L) => (Ψ.a w, Ψ.b w)) ∈
      {x : HeightOneSpectrum (𝓞 L) → ℂ × ℂ |
        (∀ w ∈ SL, x w = 0) ∧
        ∀ w ∉ SL,
          (x w).2 = HeckeEigensystem.cNorm w *
              ((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ : ℂˣ) : ℂ) ∧
          ‖(x w).1‖ ≤ ((Ideal.absNorm w.asIdeal : ℝ) + 1) *
              Real.sqrt ‖((ξL ⟨Matrix.GeneralLinearGroup.det (heckeGen (𝓞 L) L w), Subgroup.mem_top _⟩ :
                ℂˣ) : ℂ)‖ ∧
          conj (x w).1 = conj (x w).2 / ((‖(x w).2‖ : ℝ) : ℂ) * (x w).1} := by sorry
