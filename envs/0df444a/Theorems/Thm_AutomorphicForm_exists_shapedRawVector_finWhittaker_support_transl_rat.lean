-- Prove2me | Theorems.Thm_AutomorphicForm_exists_shapedRawVector_finWhittaker_support_transl_rat
-- name    : AutomorphicForm.exists_shapedRawVector_finWhittaker_support_transl_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/9629408d-b51e-58f3-9ac6-958f5cccce63
-- title:
--   Shaped raw cusp vector over ℚ with unit-shell support
-- statement:
--   The data are: a Hecke eigensystem $\Theta$ over $\mathbb{Q}$ with complex coefficients (a level ideal `Θ.level` $\neq 0$ together with families $v \mapsto \Theta.a\,v$ and $v \mapsto \Theta.b\,v$ indexed by the finite places), a character $\xi$ of the central subgroup $Z$ of the pins `productionPinsGeneral ℚ` into $\mathbb{C}^{\times}$, two finite sets $S_0 \subseteq S$ of height-one primes of $\mathcal{O}_{\mathbb{Q}}$, the hypothesis `hSlev` that no $v \notin S$ divides `Θ.level`, and a function $\varphi_0$ on $\mathrm{GL}_2$ of the adeles of $\mathbb{Q}$ with values in $\mathbb{C}$.
--
--   The hypotheses on $\varphi_0$ fall into the following groups. (i) `hiso`: $\varphi_0$ is an isotypic cusp form at these pins in the sense of `IsIsotypicCuspFormAt`, i.e. it is a smooth cuspidal automorphic function for $\xi$ (membership in the $\xi$-isotypic space attached to the pins' measure and fundamental domain, vanishing of the constant term along the unipotent, and $K_f$-smoothness), it is continuous, it is right invariant under the level subgroup `(productionPinsGeneral ℚ).U Θ.level`, for every $v \notin S_0$ it is a Hecke coset eigenfunction at the generator `(productionPinsGeneral ℚ).gen v` with eigenvalue $\Theta.a\,v$, and for every $v \notin S_0$ and every $g$ one has $\varphi_0(\mathrm{diag}(\det \mathrm{gen}\,v)\,g) = (\Theta.\mathrm{toRawCentral}.b\,v)\,\varphi_0(g)$, where $\Theta.\mathrm{toRawCentral}.b\,v = (\mathrm{cNorm}\,v)^{-1}\,\Theta.b\,v$. (ii) `hne0`: $\varphi_0 \neq 0$. (iii) `hloc`: for every finite place $p$ the local Whittaker space [`AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) psiQ p φ₀`](def/AutomorphicForm_WhittakerModelLocal.html#L19) — the $\mathbb{C}$-span of the functions $g \mapsto W_{\psi_{\mathbb{Q}}}(\varphi_0(\,\cdot\, h))(1, \text{the image of } g \text{ at } p)$ for $h$ running over $\mathrm{GL}_2$ of the adeles — satisfies three conditions: every nonzero element of it generates the whole space as the span of its right translates by $\mathrm{GL}_2(\mathbb{Q}_p)$; for every open subgroup $U$ of $\mathrm{GL}_2(\mathbb{Q}_p)$ there is a finite set $B$ of functions whose span contains every right $U$-invariant element of the space; and every element of the space is right invariant under some open subgroup. (iv) `hrep`: there is a factorizable test function $\alpha$ (a product of an archimedean factor given by a smooth compactly supported function of the matrix entries and a locally constant compactly supported finite factor) with $\mathrm{rightConv}\,\varphi_0\,\alpha = \varphi_0$. (v) `hwt`: there is $n \in \mathbb{Z}$ such that $\varphi_0$ satisfies `HasArchCharacterAt₀` at the real place of $\mathbb{Q}$ for the weight-$n$ character `archWeightCharAt`. (vi) A Whittaker factorisation: functions $W_{A,0}$ on $\mathrm{GL}_2(\mathbb{R})$ and $W_{f,0}$ on the finite-adelic subgroup `finiteAdelicGL2Subgroup ℚ` (the kernel of the archimedean projection) with `hfac₀`: the first $\psi_{\mathbb{Q}}$-Whittaker coefficient of $\varphi_0$ at $g$ equals $W_{A,0}(\mathrm{ratArchGL2}\,g)\cdot W_{f,0}(\mathrm{finFactor}\,g)$ for all $g$, together with `hWA₀`: $W_{A,0}$ is not identically zero, and `hWf1`: $W_{f,0}(1) \neq 0$. (vii) A choice $\varpi$ of an element of the valuation ring at each finite place with valuation $\exp(-1)$ (`hϖ`) and nonzero image in the completion (`hπall`), so that $\varpi_v$ is a uniformiser at $v$.
--
--   Under these hypotheses there exist a function $\varphi_1$ on $\mathrm{GL}_2$ of the adeles, a function $W_{f,1}$ on the finite-adelic subgroup, and a function $m_S$ from the finite places to $\mathbb{N}$, with the following properties.
--
--   $\varphi_1$ is continuous; $\varphi_1$ is a cuspidal automorphic function for $\xi$ at the pins `productionPinsGeneral ℚ` (in the sense of `IsCuspAutomorphicFnAt`: $\xi$-isotypic membership together with vanishing of the constant term along the unipotent); $\varphi_1$ is a finite $\mathbb{C}$-linear combination of right translates of $\varphi_0$ by finite-adelic elements, that is, there are $m \in \mathbb{N}$, scalars $c_i$ and elements $g_i$ of the finite-adelic subgroup with $\varphi_1(x) = \sum_{i} c_i\,\varphi_0(x g_i)$; for every unit $z$ of the adele ring and every $g$, $\varphi_1(\mathrm{centralScalar}(z)\,g) = \xi(z)\,\varphi_1(g)$, where $z$ is regarded as an element of the pins' central subgroup through `Subgroup.topEquiv.symm`; the $\psi_{\mathbb{Q}}$-Whittaker coefficient of $\varphi_1$ at $0$ vanishes identically; for every $g$ the family $a \mapsto \lVert W_{\psi_{\mathbb{Q}}}(\varphi_1)(a,g)\rVert$ is summable over $a \in \mathbb{Q}$; and the first Whittaker coefficient of $\varphi_1$ factorises with the same archimedean factor, namely $W_{\psi_{\mathbb{Q}}}(\varphi_1)(1,g) = W_{A,0}(\mathrm{ratArchGL2}\,g)\cdot W_{f,1}(\mathrm{finFactor}\,g)$ for all $g$.
--
--   The finite factor $W_{f,1}$ is measurable, and $\lVert W_{f,1}(n g)\rVert = \lVert W_{f,1}(g)\rVert$ for every $n$ in the subgroup [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43) of finite-adelic unipotents and every $g$. At each place $v \notin S$ there is an additive character $\psi$ of $\mathbb{Q}_v$ with $\lvert \psi \rvert \equiv 1$, trivial on the valuation ring, nontrivial on $\varpi_v^{-1}$ times the valuation ring (there is an integral $r$ with $\psi(r/\varpi_v) \neq 1$), such that $W_{f,1}(\mathrm{finFactor}(u_v(x) g)) = \psi(x)\,W_{f,1}(\mathrm{finFactor}\,g)$ for all $x \in \mathbb{Q}_v$ and all $g$, where $u_v(x)$ is the image at $v$ of the upper unipotent $\begin{pmatrix}1&x\\0&1\end{pmatrix}$. Also at each $v \notin S$: $W_{f,1} \circ \mathrm{finFactor}$ is invariant under right translation by the image at $v$ of any element of [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), and under right translation by the image at $v$ of $u_v(r)$ for integral $r$; there are elements $b_i$ of the valuation ring indexed by $i \in \mathrm{Fin}(N(v))$, $N(v)$ the absolute norm of $v$, such that for every $g$
--   $$\sum_{i} W_{f,1}\!\left(\mathrm{finFactor}\big(g \cdot \begin{pmatrix}\varpi_v & b_i\\ 0 & 1\end{pmatrix}_v\big)\right) + W_{f,1}\!\left(\mathrm{finFactor}\big(g \cdot \begin{pmatrix}1 & 0\\ 0 & \varpi_v\end{pmatrix}_v\big)\right) = \Theta.a\,v \cdot W_{f,1}(\mathrm{finFactor}\,g);$$
--   and $W_{f,1}(\mathrm{finFactor}(g \cdot (\varpi_v I)_v)) = (\Theta.b\,v / N(v))\, W_{f,1}(\mathrm{finFactor}\,g)$ for every $g$.
--
--   Finally there are three support and mass statements, all formulated for elements $g$ of the finite-adelic subgroup subject to the conditions: at every $v \notin S$ the local component $\mathrm{localAt}\,v\,g$ factors as $n' k'$ with $n'$ in the range of `unipotentGL2Hom` over $\mathbb{Q}_v$ and $k' \in$ [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178); and the bottom-row conditions that for $p \notin S$ both entries $g_{1j}$ have finite-adelic $p$-component of valuation $\le 1$, while for $p \in S$ one has $v_p(g_{10}) \le \exp(-m_S(p))$ and $v_p(g_{11} - 1) \le \exp(-m_S(p))$. First, there is a compact set $\mathrm{Cpt}$ in the finite-adelic subgroup such that every such $g$ with $W_{f,1}(g) \neq 0$ admits $n \in$ [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43) and $h \in \mathrm{Cpt}$ with $\mathrm{localAt}\,v\,(n g) = \mathrm{localAt}\,v\,h$ for all $v \in S$. Secondly, every such $g$ with $W_{f,1}(g) \neq 0$ has idele norm of $\det g$ equal to $1$. Thirdly, for every Haar measure $\mu_f$ on the finite-adelic subgroup and every Haar measure $\mu_{N}$ on `finUnipotent`, the indicator of the set of $g$ satisfying the local factorisation condition at the places outside $S$ together with the bottom-row conditions, multiplied into $g \mapsto \lVert W_{f,1}(g)\rVert^2$ viewed in $\mathbb{C}$, is integrable for the measure $\mu_f$ with density [`HaarQuotient.density finUnipotent μNFin`](def/HaarQuotient.html#L25), and the same measure of the subset of that set on which in addition $W_{f,1}(g) \neq 0$ is nonzero.
--
--   This is the finite-place half of the shaped-vector construction over $\mathbb{Q}$, preceding unitarisation: starting from a nonzero isotypic Hecke eigenform with irreducible admissible smooth local Whittaker spaces, it produces a finite combination of finite-adelic right translates whose Whittaker function has the same archimedean factor, an unramified Whittaker factor outside $S$ obeying the raw Hecke and central relations $(\Theta.a\,v,\ \Theta.b\,v/N(v))$, and a finite factor whose support modulo finite unipotents is compact on the level-$m_S$ cells at $S$ with nonvanishing $L^2$-mass. It is used in the construction of the unitary shaped vector with Whittaker factorisation and torus profile from an arithmetically genuine cuspidal realisation, on the Rankin–Selberg side of the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_shapedRawVector_finWhittaker_support_transl_rat.lean

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
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SiegelCoordinates
open AutomorphicForm
open LanglandsTunnell RSCarrier UnramifiedWhittaker
open LanglandsTunnell.RankinSelberg

theorem AutomorphicForm.exists_shapedRawVector_finWhittaker_support_transl_rat
    (Θ : HeckeEigensystem ℚ ℂ) (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (S₀ S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS₀ : S₀ ⊆ S)
    (hSlev : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ¬ v.asIdeal ∣ Θ.level)
    (φ₀ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) ξ Θ.level S₀ Θ φ₀) (hne0 : φ₀ ≠ 0)
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
    (hrep : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₀ α = φ₀)
    (hwt : ∃ n : ℤ, HasArchCharacterAt₀ ℚ (default : InfinitePlace ℚ)
      (archWeightCharAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) n) φ₀)
    (WA₀ : GL (Fin 2) ℝ → ℂ) (Wf₀ : finiteAdelicGL2Subgroup ℚ → ℂ)
    (hfac₀ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₀ 1 g =
        WA₀ (ratArchGL2 g) * Wf₀ (finFactor g))
    (hWA₀ : ∃ h : GL (Fin 2) ℝ, WA₀ h ≠ 0) (hWf1 : Wf₀ 1 ≠ 0)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ))
    (hπall : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0) :
    ∃ (φ₁ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Wf₁ : finiteAdelicGL2Subgroup ℚ → ℂ) (mS : HeightOneSpectrum (𝓞 ℚ) → ℕ),
      Continuous φ₁ ∧
      IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ₁ ∧
      (∃ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → AdelicGL2 (𝓞 ℚ) ℚ),
        (∀ i, g i ∈ finiteAdelicGL2Subgroup ℚ) ∧ φ₁ = fun x => ∑ i, c i * φ₀ (x * g i)) ∧
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ₁ (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ.comp Subgroup.topEquiv.symm.toMonoidHom z : ℂˣ) : ℂ) * φ₁ g) ∧
      (∀ g, whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₁ 0 g = 0) ∧
      (∀ g, Summable fun a : ℚ => ‖whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₁ a g‖) ∧
      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₁ 1 g = WA₀ (ratArchGL2 g) * Wf₁ (finFactor g)) ∧
      Measurable Wf₁ ∧
      (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ), ‖Wf₁ ((n : finiteAdelicGL2Subgroup ℚ) * g)‖ = ‖Wf₁ g‖) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∃ ψ : AddChar (v.adicCompletion ℚ) ℂ,
        (∀ x : v.adicCompletion ℚ, ‖ψ x‖ = 1) ∧
        (∀ r : v.adicCompletionIntegers ℚ, ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1) ∧
        (∃ r : v.adicCompletionIntegers ℚ,
          ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
            algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) ≠ 1) ∧
        ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          Wf₁ (finFactor (placeEmbed ℚ v (unipotent x) * g)) = ψ x * Wf₁ (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → Wf₁ (finFactor (g * placeEmbed ℚ v x)) = Wf₁ (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (r : v.adicCompletionIntegers ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        Wf₁ (finFactor (g * placeEmbed ℚ v
          (unipotent (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r)))) = Wf₁ (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        ∃ b : Fin (Ideal.absNorm v.asIdeal) → v.adicCompletionIntegers ℚ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          (∑ i, Wf₁ (finFactor (g * placeEmbed ℚ v
              (repSome (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (b i)))))) +
            Wf₁ (finFactor (g * placeEmbed ℚ v
              (repInf (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
          Θ.a v * Wf₁ (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        Wf₁ (finFactor (g * placeEmbed ℚ v
          (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
          (Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) * Wf₁ (finFactor g)) ∧
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
            TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (g : AdelicGL2 (𝓞 ℚ) ℚ)) = 1) ∧
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
