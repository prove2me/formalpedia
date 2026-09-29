-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCompact_support_and_ideleNorm_det_eq_one_of_shellSupport_rat
-- name    : AutomorphicForm.exists_isCompact_support_and_ideleNorm_det_eq_one_of_shellSupport_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/289cb4d9-6a25-52fc-9086-ae3bb28855af
-- title:
--   Shell vanishing forces compact support and unit idele norm
-- statement:
--   Work over $\mathbb{Q}$, with $v$ ranging over the finite places, i.e. the height-one primes of $\mathcal{O}_{\mathbb{Q}}$, and let $G_f$ denote `finiteAdelicGL2Subgroup ℚ`, the kernel of the archimedean projection $\mathrm{GL}_2(\mathbb{A}) \to \mathrm{GL}_2(\mathbb{A}_\infty)$. Given a finite set $S$ of finite places, a family $\varpi_v$ of elements of the valuation rings $\mathcal{O}_v$ whose images in $\mathbb{Q}_v$ are nonzero of valuation $\exp(-1)$, a function $W_{f_1} : G_f \to \mathbb{C}$, and exponents $m_p \in \mathbb{N}$ with $m_p \ge 1$ for $p \in S$, assume the shell-vanishing hypothesis: for each $p \in S$, $W_{f_1}(g) = 0$ whenever the $p$-component of $g$ factors as $u(x)\,\mathrm{diag}(\varpi_p^{\,n},1)\,k$ with $x \in \mathbb{Q}_p$, $n \ne 0$ and $k$ in [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) at level $p^{m_p}$ (the pullback along the local embedding of the finite level-one subgroup). Call $g \in G_f$ admissible if (i) at every $v \notin S$ its $v$-component is a product $n'k'$ with $n'$ in the image of `unipotentGL2Hom` over $\mathbb{Q}_v$ and $k'$ in `localLevelOne` at the unit ideal; (ii) $W_{f_1}(g) \neq 0$; and (iii) the bottom row of $g$ satisfies the box conditions $v_p(c) \le 1$, $v_p(d) \le 1$ for $p \notin S$, and $v_p(c) \le \exp(-m_p)$, $v_p(d-1) \le \exp(-m_p)$ for $p \in S$, the entries being read through the finite part of the adeles. The conclusion is twofold: there is a compact set $C \subseteq G_f$ such that every admissible $g$ admits $n$ in the unipotent subgroup [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43) of $G_f$ and $h \in C$ with $(ng)_v = h_v$ at every $v \in S$; and every admissible $g$ satisfies $\|\det g\| = 1$, the idele norm being the value of the Haar-modulus character.
--
--   This is the support-and-determinant bookkeeping for a finite Whittaker factor in the Kirillov-model picture: vanishing off the unit shell modulo $K_1(p^{m_p})$ at the places of $S$ confines the non-vanishing locus on the box-cut big cell to a compact set modulo unipotents, and pins the idele norm of the determinant there. It supplies the two support clauses used by [`AutomorphicForm.exists_shapedRawVector_finWhittaker_support_transl_rat`](thm.html#AutomorphicForm.exists_shapedRawVector_finWhittaker_support_transl_rat), and rests on the $K_1(p^m)$ Iwasawa-type factorisation [`AdelicDock.exists_eq_unipotent_mul_diagZ_mul_of_mem_localLevelOne_pow_of_valued_bottomRow_le`](thm.html#AdelicDock.exists_eq_unipotent_mul_diagZ_mul_of_mem_localLevelOne_pow_of_valued_bottomRow_le) together with compactness of the level-one subgroup intersected with $G_f$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCompact_support_and_ideleNorm_det_eq_one_of_shellSupport_rat.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_LanglandsTunnell_ConverseData
import Mathlib.Analysis.MellinTransform
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicFourier IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

theorem AutomorphicForm.exists_isCompact_support_and_ideleNorm_det_eq_one_of_shellSupport_rat
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ))
    (hπall : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0)
    (Wf₁ : finiteAdelicGL2Subgroup ℚ → ℂ) (mS : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hmS : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S → 1 ≤ mS p)
    (hshell : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
      ∀ (g : finiteAdelicGL2Subgroup ℚ) (x : p.adicCompletion ℚ) (n : ℤ) (k : GL (Fin 2) (p.adicCompletion ℚ)),
        k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ mS p) → n ≠ 0 →
        localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) =
          unipotent x * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπall p) n * k →
        Wf₁ g = 0) :
    (∃ Cpt : Set (finiteAdelicGL2Subgroup ℚ), IsCompact Cpt ∧
        ∀ g : finiteAdelicGL2Subgroup ℚ,
          (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
            ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') →
          Wf₁ g ≠ 0 → ((∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2,
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ 1) ∧
            (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤
                  WithZero.exp (-(mS p : ℤ)) ∧
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤
                  WithZero.exp (-(mS p : ℤ)))) →
            ∃ (n : RSCarrier.finUnipotent) (h : finiteAdelicGL2Subgroup ℚ), h ∈ Cpt ∧
              ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∈ S →
                localAt ℚ v ((((n : finiteAdelicGL2Subgroup ℚ) * g : finiteAdelicGL2Subgroup ℚ)) : AdelicGL2 (𝓞 ℚ) ℚ) =
                  localAt ℚ v (h : AdelicGL2 (𝓞 ℚ) ℚ)) ∧
      (∀ g : finiteAdelicGL2Subgroup ℚ,
          (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
            ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') →
          Wf₁ g ≠ 0 → ((∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2,
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ 1) ∧
            (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤
                  WithZero.exp (-(mS p : ℤ)) ∧
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤
                  WithZero.exp (-(mS p : ℤ)))) →
            TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) = 1) := by sorry
