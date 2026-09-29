-- Prove2me | Theorems.Thm_AutomorphicForm_exists_shapedRaw_bundle_forall_shellSupport_transl_rat
-- name    : AutomorphicForm.exists_shapedRaw_bundle_forall_shellSupport_transl_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/6489b583-5776-56f9-8894-dc78610ec8a5
-- title:
--   Simultaneous unit-shell shaping at all primes of S
-- statement:
--   Throughout, $GL_2(\mathbb{A})$ abbreviates `AdelicGL2 (𝓞 ℚ) ℚ`, the general linear group of degree two over the adele ring of $\mathbb{Q}$; `finiteAdelicGL2Subgroup ℚ` is the kernel of the archimedean projection `AdelicLevel.glArch`, i.e. the subgroup of adelic matrices with trivial archimedean component. All carrier data — the measurable structure and Haar measure on $GL_2(\mathbb{A})$, the class-representative Siegel set used as fundamental domain, the central subgroup, the level subgroups $U(N)=\mathrm{levelOne}(N)\sqcap$ `finiteAdelicGL2Subgroup ℚ`, the Hecke generators `heckeGen` and the measure on $\mathbb{A}$ — is that of `productionPinsGeneral ℚ`. Whittaker coefficients are taken with respect to the standard additive character [`NumberField.StandardAddChar.psiQ`](def/NumberField_StandardGlobalAddCharRat.html#L615) of $\mathbb{A}_{\mathbb{Q}}$ (the product of the archimedean and the finite standard characters): $\mathrm{whittakerCoefficient}(\varphi,a,g)=\int_{\mathbb{A}}\varphi(u(x)g)\,\psi_{\mathbb{Q}}(-ax)\,d\nu(x)$, where $u(x)$ is the upper unipotent matrix. For $g\in GL_2(\mathbb{A})$, `ratArchGL2 g` is the element of $GL_2(\mathbb{R})$ obtained from the archimedean component of $g$ at the unique infinite place of $\mathbb{Q}$ through the isomorphism of its completion with $\mathbb{R}$, and `finFactor g` is $\iota(\mathrm{ratArchGL2}\,g)^{-1}g$, an element of `finiteAdelicGL2Subgroup ℚ`.
--
--   The data are: a Hecke eigensystem $\Theta$ over $\mathbb{Q}$ with complex coefficients (a nonzero ideal $\Theta.\mathrm{level}$ of $\mathbb{Z}$ together with families $\Theta.a$, $\Theta.b$ indexed by the finite places); a character $\xi$ of the central subgroup of `productionPinsGeneral ℚ` with values in $\mathbb{C}^{\times}$; finite sets $S_0\subseteq S$ of finite places (hypothesis `hS₀`); a function $\varphi_0:GL_2(\mathbb{A})\to\mathbb{C}$; functions $W_{A,0}:GL_2(\mathbb{R})\to\mathbb{C}$ and $W_{f,0}$ on `finiteAdelicGL2Subgroup ℚ`; and a family $\varpi$ assigning to each finite place $v$ an element of the valuation ring of $\mathbb{Q}_v$.
--
--   The hypotheses are grouped as follows. `hSlev`: for $v\notin S$ the prime of $v$ does not divide $\Theta.\mathrm{level}$. `hiso`: $\varphi_0$ is an isotypic cusp form in the sense of `IsIsotypicCuspFormAt` for the pins, the character $\xi$, the level $\Theta.\mathrm{level}$, the exceptional set $S_0$ and the eigensystem $\Theta$; that is, $\varphi_0$ is a smooth cuspidal automorphic function (the predicates `LsXiMemberAt` for the pins data together with vanishing of the constant term along the unipotent subgroup, plus $K_f$-smoothness), is continuous, is right invariant under $U(\Theta.\mathrm{level})$, is for each $v\notin S_0$ a Hecke coset eigenfunction for the generator at $v$ with eigenvalue $\Theta.a\,v$, and satisfies $\varphi_0(z(\det \mathrm{gen}_v)g)=(\mathrm{cNorm}\,v)^{-1}\Theta.b\,v\cdot\varphi_0(g)$ for $v\notin S_0$. `hne0`: $\varphi_0\neq 0$. `hloc`: for every finite place $p$, three clauses about the local Whittaker space `WhittakerModel.localSpaceAt` at $p$ attached to $\varphi_0$ (the $\mathbb{C}$-span of the functions $h\mapsto$ the first Whittaker coefficient of a right translate of $\varphi_0$, evaluated at the local embedding of $h$): every nonzero element of that space generates it under right translation; for every open subgroup $U$ of $GL_2(\mathbb{Q}_p)$ there is a finite set $B$ of functions whose span contains all right $U$-invariant members of the space; and every member of the space is right invariant under some open subgroup. `hrep`: there is a factorizable test function $\alpha$ (an archimedean factor given by a smooth compactly supported function of the matrix entries in the mixed space, times a locally constant compactly supported finite factor) with $\mathrm{rightConv}(\varphi_0,\alpha)=\varphi_0$. `hwt`: for some integer $n$, $\varphi_0$ satisfies `HasArchCharacterAt₀` at the infinite place of $\mathbb{Q}$ for the character `archWeightCharAt` of index $n$, the $n$-th power of the weight-one character of the subgroup `rowIsometrySubgroup₀` of the completion, transported along its identification with $\mathbb{R}$. `hfac₀`: for every $g$ the first Whittaker coefficient of $\varphi_0$ factors as $W_{A,0}(\mathrm{ratArchGL2}\,g)\cdot W_{f,0}(\mathrm{finFactor}\,g)$. `hWA₀`: $W_{A,0}$ is not identically zero. `hWf1`: $W_{f,0}(1)\neq 0$. `hϖ`: each $\varpi_v$ has valuation $\exp(-1)$ in $\mathbb{Q}_v$, so is a uniformiser. `hπall`: the image of each $\varpi_v$ in $\mathbb{Q}_v$ is nonzero.
--
--   The conclusion asserts the existence of $\varphi_1:GL_2(\mathbb{A})\to\mathbb{C}$, of $W_{f,1}$ on `finiteAdelicGL2Subgroup ℚ` and of a function $m_S$ from finite places to $\mathbb{N}$ satisfying four blocks of conditions.
--
--   First, the invariant bundle (fifteen conjuncts): $\varphi_1$ is continuous; $\varphi_1$ is a cuspidal automorphic function for the pins and $\xi$ in the sense of `IsCuspAutomorphicFnAt` (the predicate `LsXiMemberAt` for the pins data together with vanishing of the constant term along the unipotent subgroup); there are $m\in\mathbb{N}$, scalars $c_i\in\mathbb{C}$ and elements $g_i\in GL_2(\mathbb{A})$, all lying in `finiteAdelicGL2Subgroup ℚ`, with $\varphi_1(x)=\sum_i c_i\varphi_0(xg_i)$; for every idele unit $z$ and every $g$, $\varphi_1(\mathrm{centralScalar}(z)\,g)=\xi(z)\varphi_1(g)$, where $z$ is read as an element of the central subgroup via `Subgroup.topEquiv.symm`; the zeroth Whittaker coefficient of $\varphi_1$ vanishes at every $g$; for every $g$ the family of norms of the Whittaker coefficients of $\varphi_1$ is summable over $a\in\mathbb{Q}$; the first Whittaker coefficient of $\varphi_1$ factors as $W_{A,0}(\mathrm{ratArchGL2}\,g)\cdot W_{f,1}(\mathrm{finFactor}\,g)$, with the same archimedean factor $W_{A,0}$; $W_{f,1}$ is measurable; $\|W_{f,1}(ng)\|=\|W_{f,1}(g)\|$ for $n$ in the unipotent subgroup [`RSCarrier.finUnipotent`](def/LanglandsTunnell_RSCarrier.html#L43) of the finite-adelic subgroup; there is an open subgroup $U$ of `finiteAdelicGL2Subgroup ℚ` under which $W_{f,1}$ is right invariant; for every finite place $v$ there is an additive character $\psi$ of $\mathbb{Q}_v$ which is unitary, trivial on the valuation ring, nontrivial on $\varpi_v^{-1}$ times the valuation ring (there is $r$ integral with $\psi(r/\varpi_v)\neq 1$), and satisfies $W_{f,1}(\mathrm{finFactor}(g\cdot \mathrm{placeEmbed}_v(u(x))))=\psi(x)\,W_{f,1}(\mathrm{finFactor}\,g)$ for all $x\in\mathbb{Q}_v$ and all $g$; for every finite place $p$ and every $g$ with trivial $p$-component, the function $h\mapsto W_{f,1}(\mathrm{finFactor}(g\cdot\mathrm{placeEmbed}_p(h)))$ lies in the local Whittaker space at $p$ attached to $\varphi_0$; there is an open subgroup $U'$ of `finiteAdelicGL2Subgroup ℚ` with $\varphi_1(gu)=\varphi_1(g)$ for all $g\in GL_2(\mathbb{A})$ and $u\in U'$; for some integer $n$, $\varphi_1$ satisfies `HasArchCharacterAt₀` at the infinite place for the weight character of index $n$; and for every $a\in\mathbb{Q}$ and every $g$ the integrand defining the $a$-th Whittaker coefficient of $\varphi_1$ is integrable.
--
--   Second, the unramified laws off $S$ (four conjuncts): for $v\notin S$, $W_{f,1}\circ\mathrm{finFactor}$ is right invariant under the image of [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤`](def/AdelicDock_LocalEmbedding.html#L178), the subgroup of $GL_2(\mathbb{Q}_v)$ whose local embedding lies in the finite-adelic level-one group at the unit ideal; for $v\notin S$ it is right invariant under $u(r)$ for every integral $r$ at $v$; for $v\notin S$ there is a family $b$ of $N(v)=\mathrm{absNorm}(v)$ integral elements such that for every $g$ the Hecke relation $$\sum_i W_{f,1}\bigl(\mathrm{finFactor}(g\cdot\mathrm{placeEmbed}_v(\mathrm{repSome}(\varpi_v,b_i)))\bigr)+W_{f,1}\bigl(\mathrm{finFactor}(g\cdot\mathrm{placeEmbed}_v(\mathrm{repInf}(\varpi_v)))\bigr)=\Theta.a\,v\cdot W_{f,1}(\mathrm{finFactor}\,g)$$ holds, where $\mathrm{repSome}(\pi,\beta)=\begin{pmatrix}\pi&\beta\\0&1\end{pmatrix}$ and $\mathrm{repInf}(\pi)=\begin{pmatrix}1&0\\0&\pi\end{pmatrix}$; and for $v\notin S$ and every $g$, right translation by the central element $\mathrm{scalarPi}(\varpi_v)=\varpi_v\cdot 1$ multiplies $W_{f,1}\circ\mathrm{finFactor}$ by $\Theta.b\,v/N(v)$.
--
--   Third, unit-shell support at every prime of $S$: for each $p\in S$ one has $1\le m_S(p)$, and for all $g$ in `finiteAdelicGL2Subgroup ℚ`, all $x\in\mathbb{Q}_p$, all integers $n\neq 0$ and all $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ m_S p)`](def/AdelicDock_LocalEmbedding.html#L178) (the subgroup of $GL_2(\mathbb{Q}_p)$ whose local embedding lies in the finite-adelic level-one group at $\mathfrak{p}^{m_S(p)}$), if the $p$-component of $g$ equals $u(x)\cdot\mathrm{diagZ}(\varpi_p,n)\cdot k$ with $\mathrm{diagZ}(\pi,n)=\begin{pmatrix}\pi^{n}&0\\0&1\end{pmatrix}$, then $W_{f,1}(g)=0$.
--
--   Fourth, $W_{f,1}(1)\neq 0$.
--
--   This is the simultaneous form of the shaping step in the construction of a Rankin–Selberg test vector: starting from an isotypic cusp form $\varphi_0$ whose first Whittaker coefficient splits into an archimedean and a finite factor, it produces a finite combination $\varphi_1$ of right translates of $\varphi_0$ by elements with trivial archimedean part whose finite Whittaker factor retains the unramified Hecke and central relations off $S$, keeps the standard invariance and growth properties, is supported in the unit shell at every prime of $S$ at the level $m_S(p)$, and is still nonzero at the identity. It is obtained by induction over $S$ from the one-prime shaping theorem [`AutomorphicForm.shapedRaw_bundle_sub_translate_unipotent_transl_rat`](thm.html#AutomorphicForm.shapedRaw_bundle_sub_translate_unipotent_transl_rat), the base case [`AutomorphicForm.shapedRaw_rawBundle_transl_rat`](thm.html#AutomorphicForm.shapedRaw_rawBundle_transl_rat) and the transport result [`AutomorphicForm.exists_unipotent_shellSupport_of_shapedRaw_bundle_transl_rat`](thm.html#AutomorphicForm.exists_unipotent_shellSupport_of_shapedRaw_bundle_transl_rat), and feeds [`AutomorphicForm.exists_shapedRawVector_finWhittaker_support_transl_rat`](thm.html#AutomorphicForm.exists_shapedRawVector_finWhittaker_support_transl_rat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_shapedRaw_bundle_forall_shellSupport_transl_rat.lean

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

theorem AutomorphicForm.exists_shapedRaw_bundle_forall_shellSupport_transl_rat
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
      (Continuous φ₁ ∧
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
      (∃ U : Subgroup (finiteAdelicGL2Subgroup ℚ), IsOpen (U : Set (finiteAdelicGL2Subgroup ℚ)) ∧
        ∀ (g : finiteAdelicGL2Subgroup ℚ) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U → Wf₁ (g * u) = Wf₁ g) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), ∃ ψ : AddChar (v.adicCompletion ℚ) ℂ,
        (∀ x : v.adicCompletion ℚ, ‖ψ x‖ = 1) ∧
        (∀ r : v.adicCompletionIntegers ℚ, ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r) = 1) ∧
        (∃ r : v.adicCompletionIntegers ℚ,
          ψ (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) r /
            algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) (ϖ v)) ≠ 1) ∧
        ∀ (x : v.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          Wf₁ (finFactor (placeEmbed ℚ v (unipotent x) * g)) = ψ x * Wf₁ (finFactor g)) ∧
      (∀ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ), localAt ℚ p g = 1 →
        (fun h : GL (Fin 2) (p.adicCompletion ℚ) => Wf₁ (finFactor (g * placeEmbed ℚ p h))) ∈
          AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p φ₀) ∧
      (∃ U' : Subgroup (finiteAdelicGL2Subgroup ℚ), IsOpen (U' : Set (finiteAdelicGL2Subgroup ℚ)) ∧
        ∀ (g : AdelicGL2 (𝓞 ℚ) ℚ) (u : finiteAdelicGL2Subgroup ℚ), u ∈ U' → φ₁ (g * (u : AdelicGL2 (𝓞 ℚ) ℚ)) = φ₁ g) ∧
      (∃ n : ℤ, HasArchCharacterAt₀ ℚ (default : InfinitePlace ℚ)
        (archWeightCharAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) n) φ₁) ∧
      (∀ (a : ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        WhittakerCoefficientIntegrable ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ φ₁ a g)) ∧
      ((∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ∀ (x : GL (Fin 2) (v.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
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
          (Θ.b v / ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)) * Wf₁ (finFactor g))) ∧
      (∀ p : HeightOneSpectrum (𝓞 ℚ), p ∈ S → 1 ≤ mS p ∧
        (∀ (g : finiteAdelicGL2Subgroup ℚ) (x : p.adicCompletion ℚ) (n : ℤ) (k : GL (Fin 2) (p.adicCompletion ℚ)),
          k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ mS p) → n ≠ 0 →
          localAt ℚ p (g : AdelicGL2 (𝓞 ℚ) ℚ) =
            unipotent x * diagZ (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) (hπall p) n * k →
          Wf₁ g = 0)) ∧
      Wf₁ 1 ≠ 0 := by sorry
