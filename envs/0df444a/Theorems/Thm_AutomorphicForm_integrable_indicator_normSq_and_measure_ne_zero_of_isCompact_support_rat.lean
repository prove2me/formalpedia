-- Prove2me | Theorems.Thm_AutomorphicForm_integrable_indicator_normSq_and_measure_ne_zero_of_isCompact_support_rat
-- name    : AutomorphicForm.integrable_indicator_normSq_and_measure_ne_zero_of_isCompact_support_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/effc3e62-cdee-54d4-93f2-4eda41da28ed
-- title:
--   Integrability and positive mass of |W_f|² on the cut
-- statement:
--   Work inside $G =$ `finiteAdelicGL2Subgroup ℚ`, the kernel of the archimedean projection `glArch` on $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$, and let `finUnipotent` be the subgroup of $G$ induced by the range of `unipotentGL2Hom` over the adeles. The data are: a finite set $S$ of height-one primes of $\mathcal{O}_{\mathbb{Q}}$; a family $\varpi_v$ of elements of the local valuation rings whose images in $\mathbb{Q}_v$ have valuation $\exp(-1)$ and are nonzero; a function $W_{f_1} : G \to \mathbb{C}$; exponents $m_S(p) \in \mathbb{N}$ with $m_S(p) \ge 1$ for $p \in S$. It is assumed that $W_{f_1}$ is measurable, that $\|W_{f_1}(ng)\| = \|W_{f_1}(g)\|$ for all $n \in$ `finUnipotent`, that $W_{f_1}$ is invariant under right translation by some open subgroup $U \le G$, that $W_{f_1}(1) \neq 0$, and (hypothesis `hCpt`) that there is a compact $\mathrm{Cpt} \subseteq G$ such that every $g$ lying in the cut and with $W_{f_1}(g) \neq 0$ satisfies $\mathrm{loc}_v(ng) = \mathrm{loc}_v(h)$ for all $v \in S$, for some $n \in$ `finUnipotent` and some $h \in \mathrm{Cpt}$. Here the cut is the set of $g$ such that (i) for every $v \notin S$ the local component $\mathrm{loc}_v(g)$ factors as $n'k'$ with $n'$ in the range of `unipotentGL2Hom` over $\mathbb{Q}_v$ and $k' \in$ [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), and (ii) the bottom row of $g$ satisfies $v_p(g_{1j}) \le 1$ for all $p \notin S$ and both $j$, while for $p \in S$ one has $v_p(g_{10}) \le \exp(-m_S(p))$ and $v_p(g_{11} - 1) \le \exp(-m_S(p))$. The conclusion asserts, for every Haar measure $\mu_f$ on $G$ and every Haar measure $\mu_N$ on `finUnipotent`, writing $\rho =$ [`HaarQuotient.density finUnipotent`](def/HaarQuotient.html#L25) $\mu_N$ for the quotient cut-off density: the indicator of the cut times $g \mapsto \mathrm{normSq}(W_{f_1}(g))$, viewed as a complex-valued function, is integrable for $\mu_f$ with density $\rho$, and the same measure of the subset of the cut where additionally $W_{f_1}(g) \neq 0$ is nonzero.
--
--   This is the analytic input making the Rankin–Selberg-type mass of a finite Whittaker factor finite and strictly positive on the level-$S$ cut of the big cell over $\mathbb{Q}$: integrability of $|W_f|^2$ against the cut-off measure of the unipotent quotient, together with non-vanishing of the mass of the non-vanishing locus. It supplies the final clause in the construction of a shaped raw vector, and is cited by [`AutomorphicForm.exists_shapedRawVector_finWhittaker_support_transl_rat`](thm.html#AutomorphicForm.exists_shapedRawVector_finWhittaker_support_transl_rat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrable_indicator_normSq_and_measure_ne_zero_of_isCompact_support_rat.lean

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
open LanglandsTunnell
open LanglandsTunnell.RankinSelberg
open RSCarrier UnramifiedWhittaker

theorem AutomorphicForm.integrable_indicator_normSq_and_measure_ne_zero_of_isCompact_support_rat
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ))
    (hπall : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0)
    (Wf₁ : finiteAdelicGL2Subgroup ℚ → ℂ) (mS : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hmS : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S → 1 ≤ mS p)
    (hWm : Measurable Wf₁)
    (hWN : ∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ), ‖Wf₁ ((n : finiteAdelicGL2Subgroup ℚ) * g)‖ = ‖Wf₁ g‖)
    (hWU : ∃ U : Subgroup (finiteAdelicGL2Subgroup ℚ), IsOpen (U : Set (finiteAdelicGL2Subgroup ℚ)) ∧
      ∀ (g : finiteAdelicGL2Subgroup ℚ) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U → Wf₁ (g * u) = Wf₁ g)
    (hW1 : Wf₁ 1 ≠ 0)
    (hCpt : ∃ Cpt : Set (finiteAdelicGL2Subgroup ℚ), IsCompact Cpt ∧
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
                  localAt ℚ v (h : AdelicGL2 (𝓞 ℚ) ℚ)) :
    (∀ (μf : Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
        (μNFin : Measure finUnipotent) [μNFin.IsHaarMeasure],
        Integrable ({g : finiteAdelicGL2Subgroup ℚ | (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
            ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') ∧ ((∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2,
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ 1) ∧
            (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤
                  WithZero.exp (-(mS p : ℤ)) ∧
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤
                  WithZero.exp (-(mS p : ℤ))))}.indicator
            fun g : finiteAdelicGL2Subgroup ℚ => (Complex.normSq (Wf₁ g) : ℂ))
          (μf.withDensity (HaarQuotient.density finUnipotent μNFin)) ∧
        (μf.withDensity (HaarQuotient.density finUnipotent μNFin))
          {g : finiteAdelicGL2Subgroup ℚ | (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
            ∃ n' ∈ (AutomorphicForm.unipotentGL2Hom (R := v.adicCompletion ℚ)).range,
              ∃ k' ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤, localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = n' * k') ∧ ((∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ S → ∀ j : Fin 2,
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j).2) p) ≤ 1) ∧
            (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S →
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 0).2) p) ≤
                  WithZero.exp (-(mS p : ℤ)) ∧
              Valued.v (((((g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 1).2) p - 1) ≤
                  WithZero.exp (-(mS p : ℤ)))) ∧ Wf₁ g ≠ 0} ≠ 0) := by sorry
