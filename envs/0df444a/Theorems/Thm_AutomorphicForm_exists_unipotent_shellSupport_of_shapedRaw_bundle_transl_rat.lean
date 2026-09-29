-- Prove2me | Theorems.Thm_AutomorphicForm_exists_unipotent_shellSupport_of_shapedRaw_bundle_transl_rat
-- name    : AutomorphicForm.exists_unipotent_shellSupport_of_shapedRaw_bundle_transl_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/66a248ea-f2f5-555f-9806-897665daa0d8
-- title:
--   Unipotent difference translate with unit-shell support at p
-- statement:
--   Fix a Hecke eigensystem $\Theta$ over $\mathbb{Q}$ with complex eigenvalues (so in particular a nonzero level ideal $\Theta.\mathrm{level}$), a character $\xi$ of the central subgroup of `productionPinsGeneral ℚ` with values in $\mathbb{C}^\times$, and a function $\varphi_0$ on $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$. The hypothesis `hloc` asserts, at every finite place $p$, three properties of the local Whittaker space `localSpaceAt` of $\varphi_0$ at $p$ (the $\mathbb{C}$-span of the functions $h \mapsto$ first Whittaker coefficient of $\varphi_0(\cdot\, g)$ evaluated at the image of $h$ under `placeEmbed`, for $g$ adelic): every nonzero member of it is a cyclic vector for right translation by $\mathrm{GL}_2(\mathbb{Q}_p)$; for each open subgroup $U$ there is a finite set spanning all $U$-right-invariant members; and each member is right invariant under some open subgroup. Further data: a function $W_{A,0}$ on $\mathrm{GL}_2(\mathbb{R})$ that is somewhere nonzero; a family $\varpi$ of integral elements of valuation $\mathrm{exp}(-1)$ at every finite place, each nonzero in the completion; a function $\varphi$ on the adelic $\mathrm{GL}_2$, a function $W_f$ on the finite-adelic subgroup (the kernel of `glArch`), and a finite place $p$. The hypothesis `hinv` packages the invariant bundle for $(\varphi, W_f)$, summarised here: $\varphi$ is continuous, is a cuspidal automorphic function for `productionPinsGeneral ℚ` with central character $\xi$ (membership in the $L$-space together with vanishing of all constant terms along the unipotent), is a finite $\mathbb{C}$-linear combination of right translates of $\varphi_0$ by elements of the finite-adelic subgroup, transforms by $\xi$ under central scalars, has vanishing zeroth Whittaker coefficient and absolutely summable Whittaker coefficients over $a \in \mathbb{Q}$, has first Whittaker coefficient factorising as $W_{A,0}(\mathrm{ratArchGL2}\,g)\cdot W_f(\mathrm{finFactor}\,g)$, is right invariant under some open subgroup, satisfies `HasArchCharacterAt₀` at the infinite place for the weight-$n$ character `archWeightCharAt` for some $n \in \mathbb{Z}$, and has integrable Whittaker integrands for all $a$ and $g$; while $W_f$ is measurable, has $|W_f|$ invariant under left translation by the finite unipotent subgroup, is right invariant under some open subgroup, satisfies at each finite place $v$ the unipotent equivariance $W_f(\mathrm{finFactor}(\mathrm{placeEmbed}\,v\,(\mathrm{unipotent}\,x)\cdot g)) = \psi(x)\,W_f(\mathrm{finFactor}\,g)$ for a unitary additive character $\psi$ trivial on the integers and nontrivial on $\varpi_v^{-1}$ times an integer, and has all its local slices $h \mapsto W_f(\mathrm{finFactor}(g\cdot\mathrm{placeEmbed}\,p\,h))$, for $g$ with trivial $p$-component, lying in the local Whittaker space of $\varphi_0$ at $p$. Finally `hlevel` says $W_f \circ \mathrm{finFactor}$ is unchanged by right multiplication by elements of [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) at $p$ for the ideal $\Theta.\mathrm{level}$, and `hW1` says $W_f(1) \neq 0$. The conclusion is the existence of $x_0$ in the completion of $\mathbb{Q}$ at $p$ with $v(x_0) \le \mathrm{exp}(1)$ such that the difference $W_f'(g) = W_f(\mathrm{finFactor}(g\cdot\mathrm{placeEmbed}\,p\,(\mathrm{unipotent}\,x_0))) - W_f(g)$ still satisfies $W_f'(1) \neq 0$, and of an integer $m_0 \ge 1$ such that for every $m' \ge m_0$ one has $W_f'(g) = 0$ whenever the $p$-component of $g$ can be written as $\mathrm{unipotent}(x)\cdot\mathrm{diagZ}(\varpi_p)(n)\cdot k$ with $n \neq 0$ and $k$ in [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) at $p$ for the ideal $p^{m'}$.
--
--   This is the one-prime shaping step in the Kirillov-model analysis of the adelic Whittaker function attached to an automorphic form on $\mathrm{GL}_2$ over $\mathbb{Q}$: a suitable unipotent difference translate at $p$ retains a nonzero value at the identity while its local support collapses to the unit shell $n = 0$ modulo deep level at $p$. It feeds the simultaneous-over-all-primes version [`AutomorphicForm.exists_shapedRaw_bundle_forall_shellSupport_transl_rat`](thm.html#AutomorphicForm.exists_shapedRaw_bundle_forall_shellSupport_transl_rat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_unipotent_shellSupport_of_shapedRaw_bundle_transl_rat.lean

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

theorem AutomorphicForm.exists_unipotent_shellSupport_of_shapedRaw_bundle_transl_rat
    (Θ : HeckeEigensystem ℚ ℂ) (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (φ₀ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hloc : (∀ p : HeightOneSpectrum (𝓞 ℚ),
              ((∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                  NumberField.StandardAddChar.psiQ p φ₀,
                W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                  NumberField.StandardAddChar.psiQ p φ₀,
                  W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) =>
                    fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) ∧
              (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
                ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ),
                  ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                    NumberField.StandardAddChar.psiQ p φ₀,
                    (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) →
                      W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
              (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ)
                  NumberField.StandardAddChar.psiQ p φ₀,
                ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧
                  ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g))))
    (WA₀ : GL (Fin 2) ℝ → ℂ) (hWA₀ : ∃ h : GL (Fin 2) ℝ, WA₀ h ≠ 0)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ))
    (hπall : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Wf : finiteAdelicGL2Subgroup ℚ → ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ))
    (hinv : Continuous φ ∧
        IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ ∧
        (∃ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → AdelicGL2 (𝓞 ℚ) ℚ),
          (∀ i, g i ∈ finiteAdelicGL2Subgroup ℚ) ∧ φ = fun x => ∑ i, c i * φ₀ (x * g i)) ∧
        (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ.comp Subgroup.topEquiv.symm.toMonoidHom z : ℂˣ) : ℂ) * φ g) ∧
        (∀ g, whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 0 g = 0) ∧
        (∀ g, Summable fun a : ℚ => ‖whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ a g‖) ∧
        (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ 1 g = WA₀ (ratArchGL2 g) * Wf (finFactor g)) ∧
        Measurable Wf ∧
        (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ), ‖Wf ((n : finiteAdelicGL2Subgroup ℚ) * g)‖ = ‖Wf g‖) ∧
        (∃ U : Subgroup (finiteAdelicGL2Subgroup ℚ), IsOpen (U : Set (finiteAdelicGL2Subgroup ℚ)) ∧
          ∀ (g : finiteAdelicGL2Subgroup ℚ) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U → Wf (g * u) = Wf g) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ ψ : AddChar (v.adicCompletion ℚ) ℂ,
          (∀ x : v.adicCompletion ℚ, ‖ψ x‖ = 1) ∧
          (∀ r : v.adicCompletionIntegers ℚ, ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1) ∧
          (∃ r : v.adicCompletionIntegers ℚ,
            ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
              algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) ≠ 1) ∧
          ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
            Wf (finFactor (placeEmbed ℚ v (unipotent x) * g)) = ψ x * Wf (finFactor g)) ∧
        (∀ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), localAt ℚ p g = 1 →
          (fun h : GL (Fin 2) (p.adicCompletion ℚ) => Wf (finFactor (g * placeEmbed ℚ p h))) ∈
            AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p φ₀) ∧
        (∃ U' : Subgroup (finiteAdelicGL2Subgroup ℚ), IsOpen (U' : Set (finiteAdelicGL2Subgroup ℚ)) ∧
          ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U' → φ (g * (u : AdelicGL2 (𝓞 ℚ) ℚ)) = φ g) ∧
        (∃ n : ℤ, HasArchCharacterAt₀ ℚ (default : InfinitePlace ℚ)
          (archWeightCharAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) n) φ) ∧
        (∀ (a : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          WhittakerCoefficientIntegrable ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ a g))
    (hlevel : ∀ (k : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p Θ.level → Wf (finFactor (g * placeEmbed ℚ p k)) = Wf (finFactor g))
    (hW1 : Wf 1 ≠ 0) :
    ∃ x₀ : p.adicCompletion ℚ, Valued.v x₀ ≤ WithZero.exp (1 : ℤ) ∧
      let Wf' : finiteAdelicGL2Subgroup ℚ → ℂ := (fun g : finiteAdelicGL2Subgroup ℚ => Wf (finFactor ((g : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p (unipotent x₀))) - Wf g)
      Wf' 1 ≠ 0 ∧
      ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m' : ℕ, m₀ ≤ m' →
        (∀ (g : finiteAdelicGL2Subgroup ℚ) (x : p.adicCompletion ℚ) (n : ℤ) (k : GL (Fin 2) (p.adicCompletion ℚ)),
          k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ m') → n ≠ 0 →
          localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) =
            unipotent x * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπall p) n * k →
          Wf' g = 0) := by sorry
