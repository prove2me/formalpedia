-- Prove2me | Theorems.Thm_AutomorphicForm_shapedRaw_bundle_sub_translate_unipotent_transl_rat
-- name    : AutomorphicForm.shapedRaw_bundle_sub_translate_unipotent_transl_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/c6547b33-f195-5465-a20a-258521e37c2c
-- title:
--   Unipotent difference translate preserves the shaped bundle at p
-- statement:
--   The setting is $GL_2$ over $\mathbb{Q}$ in adelic form: `AdelicGL2 (𝓞 ℚ) ℚ` is $GL_2$ of the adele ring of $\mathbb{Q}$, `finiteAdelicGL2Subgroup ℚ` is the kernel of the archimedean projection `glArch` (elements with trivial archimedean component), `ratArchGL2 g` is the real $GL_2$-matrix given by the component of $g$ at the unique infinite place, and `finFactor g` is the element $(\text{archRealGLAt}(\text{ratArchGL2}\,g))^{-1}g$ of that finite subgroup. Whittaker coefficients are taken with respect to the standard global additive character [`NumberField.StandardAddChar.psiQ`](def/NumberField_StandardGlobalAddCharRat.html#L615) of $\mathbb{A}_{\mathbb{Q}}$ and the data `productionPinsGeneral ℚ` (the concrete `CarrierPins` for $\mathbb{Q}$ built from the class-representative Siegel set with parameters $(1/2,1,1/2,2)$, the level subgroups $N \mapsto \mathrm{levelOne} \sqcap \mathrm{finiteAdelicGL2Subgroup}$, the Hecke generators and the adelic box), so that $\mathrm{whittakerCoefficient}\,\varphi\,\alpha\,g = \int \varphi(n(x)g)\,\psi_{\mathbb{Q}}(-\alpha x)$ against the pins' measure on the adeles; for $x$ in a field, `unipotent x` is $\begin{pmatrix}1&x\\0&1\end{pmatrix}$, `diagZ π hπ n` is $\mathrm{diag}(\pi^{n},1)$, `repSome π hπ β` is $\begin{pmatrix}\pi&\beta\\0&1\end{pmatrix}$, `repInf π hπ` is $\begin{pmatrix}1&0\\0&\pi\end{pmatrix}$, `scalarPi π hπ` is $\pi\cdot I$, `placeEmbed ℚ v` is the embedding $GL_2(\mathbb{Q}_v)\to GL_2(\mathbb{A}_{\mathbb{Q}})$ at a finite place $v$, `localAt ℚ v` is the projection to the component at $v$, and [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v N`](def/AdelicDock_LocalEmbedding.html#L178) is the subgroup of $GL_2(\mathbb{Q}_v)$ whose image under `localEmbed` satisfies the level-$N$ condition `finiteLevelOne`.
--
--   The data are: a Hecke eigensystem $\Theta$ over $\mathbb{C}$ for $\mathbb{Q}$ (a nonzero level ideal $\Theta.\mathrm{level}$ together with families $\Theta.a$, $\Theta.b$ of complex numbers indexed by the finite places); a character $\xi$ of the central subgroup $(\mathrm{productionPinsGeneral}\ \mathbb{Q}).Z$ with values in $\mathbb{C}^{\times}$; a finite set $S$ of finite places; a base function $\varphi_0 : GL_2(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$; a function $W_{A_0} : GL_2(\mathbb{R})\to\mathbb{C}$; a choice $\varpi$ of a local integer at every finite place; further functions $\varphi : GL_2(\mathbb{A}_{\mathbb{Q}})\to\mathbb{C}$ and $W_f : \mathrm{finiteAdelicGL2Subgroup}\,\mathbb{Q}\to\mathbb{C}$; a finite place $p$ with $p\in S$ and an element $x_0\in\mathbb{Q}_p$; finite sets $T$, $T'$ of finite places with $p\notin T'$; and a function $m$ from finite places to $\mathbb{N}$.
--
--   The hypotheses on the base datum are: $\varphi_0$ is continuous (`hφ₀c`); $\varphi_0$ satisfies `IsCuspAutomorphicFnAt` for the pins and $\xi$, i.e. it lies in the space `LsXiMemberAt` determined by those pins and $\xi$ and its constant term along the adelic unipotent subgroup vanishes identically (`hφ₀`); and $\varphi_0$ is reproduced by right convolution against some factorisable test function, i.e. there is $\alpha$ with `IsFactorizableTestFn ℚ α` (a product of a smooth compactly supported archimedean factor and a locally constant compactly supported finite factor) and $\mathrm{rightConv}\,\varphi_0\,\alpha = \varphi_0$ (`hrep₀`). Further, $W_{A_0}$ is not identically zero (`hWA₀`); and $\varpi$ is a uniformiser at every place in the sense that its valuation in $\mathbb{Q}_v$ is $\exp(-1)$ (`hϖ`) and its image in $\mathbb{Q}_v$ is nonzero (`hπall`).
--
--   The hypothesis `hinv` (the invariant bundle, fifteen clauses) asserts: (i) $\varphi$ is continuous; (ii) $\varphi$ satisfies `IsCuspAutomorphicFnAt` for the pins and $\xi$; (iii) $\varphi$ is a finite linear combination $\varphi(x) = \sum_i c_i\,\varphi_0(x g_i)$ of right translates of $\varphi_0$ by elements $g_i$ of the finite-adelic subgroup; (iv) $\varphi(\mathrm{centralScalar}(z)g) = \xi(z)\varphi(g)$ for every idele unit $z$ and every $g$, where $\xi$ is read off through `Subgroup.topEquiv.symm`; (v) the zeroth Whittaker coefficient of $\varphi$ vanishes at every $g$; (vi) for every $g$ the family $a\mapsto \|\mathrm{whittakerCoefficient}\,\varphi\,a\,g\|$ is summable over $a\in\mathbb{Q}$; (vii) the first Whittaker coefficient factorises as $\mathrm{whittakerCoefficient}\,\varphi\,1\,g = W_{A_0}(\mathrm{ratArchGL2}\,g)\cdot W_f(\mathrm{finFactor}\,g)$ for all $g$; (viii) $W_f$ is measurable; (ix) $\|W_f(n g)\| = \|W_f(g)\|$ for $n$ in [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43) (the adelic unipotent subgroup viewed inside the finite-adelic subgroup) and $g$ in the finite-adelic subgroup; (x) there is an open subgroup $U$ of the finite-adelic subgroup with $W_f(gu)=W_f(g)$ for $u\in U$; (xi) for every finite place $v$ there is an additive character $\psi$ of $\mathbb{Q}_v$ which is unitary, trivial on the local integers, nontrivial on $\varpi_v^{-1}\mathcal{O}_v$ (some local integer $r$ has $\psi(r/\varpi_v)\neq 1$), and satisfies $W_f(\mathrm{finFactor}(\mathrm{placeEmbed}\,v\,(\mathrm{unipotent}\,x)\cdot g)) = \psi(x)\,W_f(\mathrm{finFactor}\,g)$ for all $x\in\mathbb{Q}_v$ and all $g$; (xii) for every finite place and every $g$ whose component there is trivial, the function $h\mapsto W_f(\mathrm{finFactor}(g\cdot\mathrm{placeEmbed}\,h))$ lies in [`AutomorphicForm.WhittakerModel.localSpaceAt`](def/AutomorphicForm_WhittakerModelLocal.html#L19) at that place for $\varphi_0$, i.e. in the complex span of the local Whittaker functions attached to right translates of $\varphi_0$; (xiii) there is an open subgroup $U'$ of the finite-adelic subgroup with $\varphi(gu)=\varphi(g)$ for all $g$ and all $u\in U'$; (xiv) there is $n\in\mathbb{Z}$ such that $\varphi$ satisfies `HasArchCharacterAt₀` at the real place of $\mathbb{Q}$ for the character `archWeightCharAt … n`, the $n$-th power of the weight-one character on `rowIsometrySubgroup₀`; (xv) all Whittaker coefficient integrands of $\varphi$ are integrable, for every $a\in\mathbb{Q}$ and every $g$.
--
--   The hypothesis `hoff` (the unramified laws off $S$, four clauses) asserts, for every finite place $v\notin S$: (a) $W_f(\mathrm{finFactor}(g\cdot\mathrm{placeEmbed}\,v\,x)) = W_f(\mathrm{finFactor}\,g)$ for $x$ in the local level subgroup at $v$ for the ideal $\top$; (b) the same invariance for $x = \mathrm{unipotent}(r)$ with $r$ a local integer; (c) there are representatives $b : \mathrm{Fin}(\mathrm{Ideal.absNorm}\,v) \to \mathcal{O}_v$ such that for all $g$, $\sum_i W_f(\mathrm{finFactor}(g\cdot\mathrm{placeEmbed}\,v\,(\mathrm{repSome}\,\varpi_v\,b_i))) + W_f(\mathrm{finFactor}(g\cdot\mathrm{placeEmbed}\,v\,(\mathrm{repInf}\,\varpi_v))) = \Theta.a\,v \cdot W_f(\mathrm{finFactor}\,g)$; (d) $W_f(\mathrm{finFactor}(g\cdot\mathrm{placeEmbed}\,v\,(\mathrm{scalarPi}\,\varpi_v))) = (\Theta.b\,v/\mathrm{Ideal.absNorm}\,v)\cdot W_f(\mathrm{finFactor}\,g)$. The hypothesis `hlevel` asserts that for every $q\in T$, $W_f$ is right invariant under $\mathrm{placeEmbed}\,q\,k$ for $k$ in the local level subgroup at $q$ for the ideal $\Theta.\mathrm{level}$. The hypothesis `hshell` (shell support at $T'$) asserts that for every $q\in T'$ and every $g$ in the finite-adelic subgroup: whenever $\mathrm{localAt}\,q\,g = \mathrm{unipotent}(x)\cdot\mathrm{diagZ}(\varpi_q, n)\cdot k$ with $n\neq 0$ and $k$ in the local level subgroup at $q$ for the ideal $q^{m(q)}$, then $W_f(g)=0$.
--
--   Set $\varphi'(g) := \varphi(g\cdot\mathrm{placeEmbed}\,p\,(\mathrm{unipotent}\,x_0)) - \varphi(g)$ and, for $g$ in the finite-adelic subgroup, $W_f'(g) := W_f(\mathrm{finFactor}(g\cdot\mathrm{placeEmbed}\,p\,(\mathrm{unipotent}\,x_0))) - W_f(g)$. The conclusion is a conjunction of four parts.
--
--   First, the pair $(\varphi', W_f')$ satisfies the fifteen clauses of the invariant bundle, with the same $\varphi_0$, $\xi$ and $W_{A_0}$ and with the existential data re-chosen: $\varphi'$ is continuous; $\varphi'$ satisfies `IsCuspAutomorphicFnAt` for the pins and $\xi$; $\varphi'$ is a finite linear combination $\sum_i c_i\varphi_0(\,\cdot\,g_i)$ of right translates of $\varphi_0$ by elements of the finite-adelic subgroup; $\varphi'(\mathrm{centralScalar}(z)g) = \xi(z)\varphi'(g)$; the zeroth Whittaker coefficient of $\varphi'$ vanishes at every $g$; the norms of the Whittaker coefficients of $\varphi'$ are summable over $a\in\mathbb{Q}$ for every $g$; $\mathrm{whittakerCoefficient}\,\varphi'\,1\,g = W_{A_0}(\mathrm{ratArchGL2}\,g)\cdot W_f'(\mathrm{finFactor}\,g)$ for all $g$; $W_f'$ is measurable; $\|W_f'(ng)\| = \|W_f'(g)\|$ for $n$ in [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43); there is an open subgroup $U$ with $W_f'(gu)=W_f'(g)$ for $u\in U$; for every finite place $v$ there is a unitary additive character $\psi$ of $\mathbb{Q}_v$, trivial on the local integers and nontrivial on $\varpi_v^{-1}\mathcal{O}_v$, with $W_f'(\mathrm{finFactor}(\mathrm{placeEmbed}\,v\,(\mathrm{unipotent}\,x)\cdot g)) = \psi(x)W_f'(\mathrm{finFactor}\,g)$; for every finite place and every $g$ with trivial component there, the function $h\mapsto W_f'(\mathrm{finFactor}(g\cdot\mathrm{placeEmbed}\,h))$ lies in `localSpaceAt` at that place for $\varphi_0$; there is an open subgroup $U'$ with $\varphi'(gu)=\varphi'(g)$ for $u\in U'$; there is $n\in\mathbb{Z}$ for which $\varphi'$ satisfies `HasArchCharacterAt₀` at the real place with the weight character `archWeightCharAt … n`; and all Whittaker integrands of $\varphi'$ are integrable, for every $a\in\mathbb{Q}$ and every $g$.
--
--   Second, $W_f'$ satisfies the four unramified laws off $S$ in the same form as `hoff`: right invariance at $v\notin S$ under the local level subgroup for $\top$, right invariance under integral unipotents, a Hecke relation at $v$ with eigenvalue $\Theta.a\,v$ for suitable representatives $b$, and the scalar relation with factor $\Theta.b\,v/\mathrm{Ideal.absNorm}\,v$.
--
--   Third, $W_f'$ is right invariant under $\mathrm{placeEmbed}\,q\,k$ for $k$ in the local level subgroup at $q$ for $\Theta.\mathrm{level}$, for every $q\in T$ with $q\neq p$ — level invariance is retained at the primes of $T$ other than $p$.
--
--   Fourth, $W_f'$ has the shell-support property at every $q\in T'$: if $g$ lies in the finite-adelic subgroup and $\mathrm{localAt}\,q\,g = \mathrm{unipotent}(x)\cdot\mathrm{diagZ}(\varpi_q,n)\cdot k$ with $n\neq 0$ and $k$ in the local level subgroup at $q$ for $q^{m(q)}$, then $W_f'(g)=0$.
--
--   This is one shaping step in the adelic Whittaker analysis of $GL_2/\mathbb{Q}$: forming the difference of a form and its translate by a unipotent element at a prime $p\in S$ transports the whole invariant bundle (automorphy, central and archimedean characters, Whittaker factorisation, local Whittaker-model membership), the unramified Hecke laws off $S$ and the shell-support conditions at $T'$, while level invariance survives at the primes of $T$ other than $p$. It is used by [`AutomorphicForm.exists_shapedRaw_bundle_forall_shellSupport_transl_rat`](thm.html#AutomorphicForm.exists_shapedRaw_bundle_forall_shellSupport_transl_rat), where such steps are iterated to produce shell support at all prescribed primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_shapedRaw_bundle_sub_translate_unipotent_transl_rat.lean

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
open LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier UnramifiedWhittaker

theorem AutomorphicForm.shapedRaw_bundle_sub_translate_unipotent_transl_rat
    (Θ : HeckeEigensystem ℚ ℂ) (ξ : (productionPinsGeneral ℚ).Z →* ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (φ₀ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hφ₀c : Continuous φ₀) (hφ₀ : IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ₀)
    (hrep₀ : ∃ α : AdelicGL2 (𝓞 ℚ) ℚ → ℂ, IsFactorizableTestFn ℚ α ∧ rightConv ℚ φ₀ α = φ₀)
    (WA₀ : GL (Fin 2) ℝ → ℂ) (hWA₀ : ∃ h : GL (Fin 2) ℝ, WA₀ h ≠ 0)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ), v.adicCompletionIntegers ℚ)
    (hϖ : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      Valued.v (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) = WithZero.exp (-1 : ℤ))
    (hπall : ∀ v : HeightOneSpectrum (𝓞 ℚ),
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v) ≠ 0)
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (Wf : finiteAdelicGL2Subgroup ℚ → ℂ)
    (p : HeightOneSpectrum (𝓞 ℚ)) (hp : p ∈ S) (x₀ : p.adicCompletion ℚ)
    (T T' : Finset (HeightOneSpectrum (𝓞 ℚ))) (hpT' : p ∉ T') (m : HeightOneSpectrum (𝓞 ℚ) → ℕ)
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
    (hoff : (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → Wf (finFactor (g * placeEmbed ℚ v x)) = Wf (finFactor g)) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (r : v.adicCompletionIntegers ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          Wf (finFactor (g * placeEmbed ℚ v
            (unipotent (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r)))) = Wf (finFactor g)) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
          ∃ b : Fin (Ideal.absNorm v.asIdeal) → v.adicCompletionIntegers ℚ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
            (∑ i, Wf (finFactor (g * placeEmbed ℚ v
                (repSome (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)
                  (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (b i)))))) +
              Wf (finFactor (g * placeEmbed ℚ v
                (repInf (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
            Θ.a v * Wf (finFactor g)) ∧
        (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          Wf (finFactor (g * placeEmbed ℚ v
            (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
            (Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) * Wf (finFactor g)))
    (hlevel : (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ T → ∀ (k : GL (Fin 2) (p.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p Θ.level → Wf (finFactor (g * placeEmbed ℚ p k)) = Wf (finFactor g)))
    (hshell : ∀ q : HeightOneSpectrum (𝓞 ℚ), q ∈ T' →
      (∀ (g : finiteAdelicGL2Subgroup ℚ) (x : q.adicCompletion ℚ) (n : ℤ) (k : GL (Fin 2) (q.adicCompletion ℚ)),
            k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ q (q.asIdeal ^ m q) → n ≠ 0 →
            localAt ℚ q (g : AdelicGL2 (𝓞 ℚ) ℚ) =
              unipotent x * diagZ (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ) (ϖ q)) (hπall q) n * k →
            Wf g = 0)) :
    let φ' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ := (fun g : AdelicGL2 (𝓞 ℚ) ℚ => φ (g * placeEmbed ℚ p (unipotent x₀)) - φ g)
    let Wf' : finiteAdelicGL2Subgroup ℚ → ℂ := (fun g : finiteAdelicGL2Subgroup ℚ => Wf (finFactor ((g : AdelicGL2 (𝓞 ℚ) ℚ) * placeEmbed ℚ p (unipotent x₀))) - Wf g)
    (Continuous φ' ∧
      IsCuspAutomorphicFnAt ℚ (productionPinsGeneral ℚ) ξ φ' ∧
      (∃ (m : ℕ) (c : Fin m → ℂ) (g : Fin m → AdelicGL2 (𝓞 ℚ) ℚ),
        (∀ i, g i ∈ finiteAdelicGL2Subgroup ℚ) ∧ φ' = fun x => ∑ i, c i * φ₀ (x * g i)) ∧
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ), φ' (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ.comp Subgroup.topEquiv.symm.toMonoidHom z : ℂˣ) : ℂ) * φ' g) ∧
      (∀ g, whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ' 0 g = 0) ∧
      (∀ g, Summable fun a : ℚ => ‖whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ' a g‖) ∧
      (∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        whittakerCoefficient ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ' 1 g = WA₀ (ratArchGL2 g) * Wf' (finFactor g)) ∧
      Measurable Wf' ∧
      (∀ (n : RSCarrier.finUnipotent) (g : finiteAdelicGL2Subgroup ℚ), ‖Wf' ((n : finiteAdelicGL2Subgroup ℚ) * g)‖ = ‖Wf' g‖) ∧
      (∃ U : Subgroup (finiteAdelicGL2Subgroup ℚ), IsOpen (U : Set (finiteAdelicGL2Subgroup ℚ)) ∧
        ∀ (g : finiteAdelicGL2Subgroup ℚ) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U → Wf' (g * u) = Wf' g) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ ψ : AddChar (v.adicCompletion ℚ) ℂ,
        (∀ x : v.adicCompletion ℚ, ‖ψ x‖ = 1) ∧
        (∀ r : v.adicCompletionIntegers ℚ, ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1) ∧
        (∃ r : v.adicCompletionIntegers ℚ,
          ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
            algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) ≠ 1) ∧
        ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          Wf' (finFactor (placeEmbed ℚ v (unipotent x) * g)) = ψ x * Wf' (finFactor g)) ∧
      (∀ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), localAt ℚ p g = 1 →
        (fun h : GL (Fin 2) (p.adicCompletion ℚ) => Wf' (finFactor (g * placeEmbed ℚ p h))) ∈
          AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p φ₀) ∧
      (∃ U' : Subgroup (finiteAdelicGL2Subgroup ℚ), IsOpen (U' : Set (finiteAdelicGL2Subgroup ℚ)) ∧
        ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U' → φ' (g * (u : AdelicGL2 (𝓞 ℚ) ℚ)) = φ' g) ∧
      (∃ n : ℤ, HasArchCharacterAt₀ ℚ (default : InfinitePlace ℚ)
        (archWeightCharAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) n) φ') ∧
      (∀ (a : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        WhittakerCoefficientIntegrable ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ' a g)) ∧
    ((∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤ → Wf' (finFactor (g * placeEmbed ℚ v x)) = Wf' (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (r : v.adicCompletionIntegers ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        Wf' (finFactor (g * placeEmbed ℚ v
          (unipotent (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r)))) = Wf' (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
        ∃ b : Fin (Ideal.absNorm v.asIdeal) → v.adicCompletionIntegers ℚ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          (∑ i, Wf' (finFactor (g * placeEmbed ℚ v
              (repSome (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)
                (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (b i)))))) +
            Wf' (finFactor (g * placeEmbed ℚ v
              (repInf (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
          Θ.a v * Wf' (finFactor g)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        Wf' (finFactor (g * placeEmbed ℚ v
          (scalarPi (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) (hπall v)))) =
          (Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) * Wf' (finFactor g))) ∧
    (∀ q : HeightOneSpectrum (𝓞 ℚ), q ∈ T → q ≠ p → ∀ (k : GL (Fin 2) (q.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ q Θ.level → Wf' (finFactor (g * placeEmbed ℚ q k)) = Wf' (finFactor g)) ∧
    (∀ q : HeightOneSpectrum (𝓞 ℚ), q ∈ T' →
      (∀ (g : finiteAdelicGL2Subgroup ℚ) (x : q.adicCompletion ℚ) (n : ℤ) (k : GL (Fin 2) (q.adicCompletion ℚ)),
          k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ q (q.asIdeal ^ m q) → n ≠ 0 →
          localAt ℚ q (g : AdelicGL2 (𝓞 ℚ) ℚ) =
            unipotent x * diagZ (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ) (ϖ q)) (hπall q) n * k →
          Wf' g = 0)) := by sorry
