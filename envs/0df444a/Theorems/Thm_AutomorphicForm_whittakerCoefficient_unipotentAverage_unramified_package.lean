-- Prove2me | Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentAverage_unramified_package
-- name    : AutomorphicForm.whittakerCoefficient_unipotentAverage_unramified_package
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/47d87106-a6d0-59b6-80e1-fbd379f9c33c
-- title:
--   Transfer of unramified Whittaker data to a Schwartz–Bruhat average
-- statement:
--   Let $F$ be a number field. Fix real parameters $c,u,d_1,d_2$ with $d_1<d_2$ (`hd`) and a finite set $T$ of elements of $\mathrm{GL}_2(\mathbb{A}_F)$ (written `AdelicGL2 (𝓞 F) F`), and let
--   $$D \;=\; \bigcup_{x\in T}\;(\,\cdot\,*x)\bigl(\,\mathrm{centreCutSiegelSet}\,F\,c\,u\,d_1\,d_2\,\bigr)$$
--   be the union of the right translates by the elements of $T$ of the centre-cut Siegel set, namely of the set of $g$ whose finite part `glFin (𝓞 F) F g` lies in `finiteIntegralGL2 (𝓞 F) F`, whose archimedean component at each infinite place $w$ satisfies $c \le$ `localHeight` $=\lVert\det\rVert/$`rowNormSq` and `xWindowSq` $=$ `topNormSq`$/$`rowNormSq` $-$ `localHeight`$^2 \le u^2$, and with `archDetNorm` $w\,g \in [d_1,d_2]$ for every $w$. The hypothesis `hcov` asserts `CoversModCentre F D`: every $g\in\mathrm{GL}_2(\mathbb{A}_F)$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma\, g\, z\cdot 1 \in D$, the images being taken through `globalPoints` and the central embedding `centralScalar`.
--
--   All Whittaker coefficients and automorphy conditions below are taken at the carrier data $P=$ `productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)`: the Borel $\sigma$-algebra and Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, the window $D$, the central group $\mathbb{Z} = \top$ (the whole idele unit group), the level groups $N \mapsto$ `levelOne (𝓞 F) F N` intersected with the kernel `finiteAdelicGL2Subgroup F` of `glArch`, the Hecke generators $v\mapsto$ `heckeGen (𝓞 F) F v` $=\operatorname{diag}(\varpi_v,1)$ placed at $v$, the Borel $\sigma$-algebra on $\mathbb{A}_F$, and for the additive measure the Haar measure `adelicAddHaar` conditioned on the box `adelicBox F`.
--
--   Further data and hypotheses: a Hecke eigensystem $\Phi$ over $\mathbb{C}$ (a level ideal $\Phi.\mathrm{level}\neq\bot$ and families of eigenvalues $\Phi.a$, $\Phi.b$ indexed by the finite places); a homomorphism $\xi$ from $P.Z$ to $\mathbb{C}^\times$; a function $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ with `hφ` asserting `IsCuspAutomorphicFnAt F P ξ φ`, i.e. $\varphi$ satisfies the predicate `LsXiMemberAt` for the measure, window and central character data of $P$ and is cuspidal in the sense that its constant term $\int \varphi(n(x)g)$ against the conditioned measure $P.\nu$ vanishes for every $g$, where $n(x)=$ `unipotentGL2 x` $=\begin{pmatrix}1&x\\0&1\end{pmatrix}$; continuity of $\varphi$ (`hcont`); a test function $f$ with `hf` asserting `IsFactorizableTestFn F f`, that is $f(g)=f_\infty(\mathrm{glArch}\,g)\,f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_\infty$ smooth in the matrix entries and compactly supported and $f_{\mathrm{fin}}$ locally constant and compactly supported; a global additive character $\psi$ of $\mathbb{A}_F$ with `hψ` asserting `IsGlobalAddChar F ψ` (trivial on $F$, continuous, non-trivial); and a finite set $S$ of finite places of $F$.
--
--   The smoothed form is `rightConv F φ f`$(g)=\int \varphi(gx) f(x)\,dx$ against the Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$. It is assumed: `hlev`, right invariance of `rightConv F φ f` under every $k$ in `levelOne (𝓞 F) F Φ.level ⊓ finiteAdelicGL2Subgroup F`; `hKS`, for every $v\notin S$ right invariance under the image at $v$ of $\mathrm{GL}_2(\mathcal{O}_v)$; `hHecke`, for every $v\notin S$ the predicate `IsHeckeCosetEigenfunctionAt` for the level group `levelOne (𝓞 F) F Φ.level ⊓ finiteAdelicGL2Subgroup F`, the generator `heckeGen (𝓞 F) F v` and the eigenvalue $\Phi.a\,v$, i.e. there are $N(v)+1$ representatives forming a Hecke coset system whose coset sum $g\mapsto\sum_i \mathrm{rightConv}(g\,\mathrm{reps}_i)$ equals $\Phi.a\,v$ times `rightConv F φ f`; and `hcentral`, for every $v\notin S$ and every $g$, $\mathrm{rightConv}(\mathrm{centralScalar}(\det \mathrm{heckeGen}\,v)\,g)=\Phi.\mathrm{toRawCentral}.b\,v\cdot\mathrm{rightConv}(g)$, where $\Phi.\mathrm{toRawCentral}.b\,v=(\mathrm{N}v)^{-1}\Phi.b\,v$ with $\mathrm{N}v$ the absolute norm of $v$.
--
--   Local characters and Hecke representatives: a family $\psi_v$ of additive characters of the completions $F_v$; `hNc`, for every $v\notin S$, every $x\in F_v$, every $g$, and every $W$ which is left invariant under $n(\beta)$ for $\beta\in F$, the first Whittaker coefficient at $P$ satisfies $W_1(W)\bigl(n_v(x)\,g\bigr)=\psi_v(x)\,W_1(W)(g)$, where $W_1(W)(g)=\int W(n(x)g)\,\psi(-x)\,d\nu(x)$ for the conditioned measure; elements $\varpi_v\in\mathcal{O}_v$ with `hπ` their non-vanishing in $F_v$; finite non-empty index types $I(v)$ with a family $b_v : I(v)\to\mathcal{O}_v$; `hI`, $\#I(v)=\mathrm{N}v$ for $v\notin S$; and `hsys`, for $v\notin S$ the family indexed by `Option (I v)` sending `none` to the image at $v$ of $\mathrm{repInf}=\begin{pmatrix}1&0\\0&\varpi_v\end{pmatrix}$ and `some j` to the image at $v$ of $\mathrm{repSome}=\begin{pmatrix}\varpi_v&b_v(j)\\0&1\end{pmatrix}$ is a Hecke coset system for the level group and `heckeGen (𝓞 F) F v`: each member lies in the double coset $U\,g\,U$, the members meet every left coset contained in it, and their classes in $G/U$ are pairwise distinct.
--
--   Two further hypotheses: `hnormU`, every idele unit $u$ whose archimedean component is $1$, whose components at the places of $S$ are $1$, and whose finite part lies in [`IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F`](def/IsDedekindDomain_FiniteUnitIdeles.html#L9) (integral with integral inverse at every finite place), has `ideleNorm F u = 1`; and $g_0\in\mathrm{GL}_2(\mathbb{A}_F)$ with `hg₀` asserting that all matrix entries of $g_0$ agree with those of the identity at every $v\notin S$.
--
--   Finally, $B:\mathbb{A}_F\to\mathbb{C}$ lies in the Schwartz–Bruhat space [`NumberField.AdelicFourier.schwartzBruhat F`](def/NumberField_AdelicFourier.html#L80) (`hB`), and `hBstd` asserts the existence of local factors $B_i$ at the infinite places and $B_f$ at the finite places with `IsFactorizableStandardOutside B S Bi Bf`, i.e. $B$ is the indicator of `integralOutside S` times $\bigl(\prod_w B_i(w)(x_w)\bigr)\prod_{v\in S}B_f(v)(x_v)$. The function $\Phi_B$ is specified by `hΦB`: for all $h$,
--   $$\Phi_B(h)=\int_{\mathbb{A}_F} B(x)\,\bigl(\mathrm{rightConv}\,F\,\varphi\,(y\mapsto f(g_0^{-1}y))\bigr)\bigl(h\,n(x)\bigr)\,dx$$
--   against the adelic additive Haar measure; note that the convolution here is taken with the left translate $y\mapsto f(g_0^{-1}y)$ of the test function.
--
--   Writing $W=$ `whittakerCoefficient F P ψ ΦB 1`, the first Whittaker coefficient of $\Phi_B$ at $\alpha=1$, the conclusion is the conjunction of five statements.
--
--   (i) For every $v\notin S$, every $x\in F_v$ and every $g\in\mathrm{GL}_2(\mathbb{A}_F)$: $W\bigl(n_v(x)\,g\bigr)=\psi_v(x)\,W(g)$, where $n_v(x)$ is the image at $v$ of $\mathrm{unipotent}\,x$.
--
--   (ii) For every $v\notin S$, every $r\in\mathcal{O}_v$ and every $g$: $W\bigl(g\,n_v(r)\bigr)=W(g)$.
--
--   (iii) For every $v\notin S$ and every $g$:
--   $$\sum_{i\in I(v)} W\Bigl(g\cdot \begin{pmatrix}\varpi_v&b_v(i)\\0&1\end{pmatrix}_v\Bigr)\;+\;W\Bigl(g\cdot\begin{pmatrix}1&0\\0&\varpi_v\end{pmatrix}_v\Bigr)=\Phi.a\,v\cdot W(g),$$
--   the matrices being placed at $v$ by `placeEmbed`.
--
--   (iv) For every $v\notin S$ and every $g$: $W\bigl(g\cdot \mathrm{scalarPi}(\varpi_v)_v\bigr)=\Phi.\mathrm{toRawCentral}.b\,v\cdot W(g)$, where $\mathrm{scalarPi}(\varpi_v)=\varpi_v\cdot 1_2$ placed at $v$ and $\Phi.\mathrm{toRawCentral}.b\,v=(\mathrm{N}v)^{-1}\Phi.b\,v$.
--
--   (v) For every idele unit $w$ whose archimedean component is $1$, whose components at the places of $S$ are $1$ and whose finite part lies in `unitIdeles (𝓞 F) F`, and for every $g$: $W\bigl(g\cdot \mathrm{diagOne}\,w\bigr)=W(g)$, where $\mathrm{diagOne}\,w=\operatorname{diag}(w,1)$.
--
--   This is the transfer step which shows that the five unramified local conditions imposed on a smoothed cuspidal function — left $\psi_v$-equivariance, right $n(\mathcal{O}_v)$-invariance, the Hecke relation with eigenvalue $a_v$, the central relation with $(\mathrm{N}v)^{-1}b_v$, and invariance under $\operatorname{diag}(w,1)$ for unit ideles trivial at $S$ and at the infinite places — survive passage to the first Whittaker coefficient of the unipotent average of the function against a Schwartz–Bruhat kernel twisted by $g_0$. It supplies the unramified input to [`AutomorphicForm.exists_differentiable_hasProd_eulerProduct_twist_of_isArithGenuineCuspRealizable`](thm.html#AutomorphicForm.exists_differentiable_hasProd_eulerProduct_twist_of_isArithGenuineCuspRealizable), where the Euler product of the associated $L$-series is assembled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_whittakerCoefficient_unipotentAverage_unramified_package.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_CentreCutSiegelSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix MeasureTheory Polynomial
open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdeleRing NumberField.TateGlobal NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp AdelicDock UnramifiedWhittaker

theorem AutomorphicForm.whittakerCoefficient_unipotentAverage_unramified_package
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂) (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Φ : HeckeEigensystem F ℂ)
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsCuspAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ)
    (hcont : Continuous φ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hlev : ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ levelOne (𝓞 F) F Φ.level ⊓ finiteAdelicGL2Subgroup F,
      rightConv F φ f (g * k) = rightConv F φ f g)
    (hKS : ∀ v ∉ S, ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers F)) (g : AdelicGL2 (𝓞 F) F),
        rightConv F φ f (g * placeEmbed F v
          (Matrix.GeneralLinearGroup.map
            (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) kv)) = rightConv F φ f g)
    (ψv : ∀ v : HeightOneSpectrum (𝓞 F), AddChar (v.adicCompletion F) ℂ)
    (hNc : ∀ v ∉ S, ∀ (x : v.adicCompletion F) (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) (W : AdelicGL2 (𝓞 F) F → ℂ),
        (∀ (β : F) (h : AdelicGL2 (𝓞 F) F),
          W (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * h) = W h) →
        whittakerCoefficient F
          (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ W 1 (placeEmbed F v (unipotent x) * g) =
        ψv v x * whittakerCoefficient F
          (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ W 1 g)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F)
    (hπ : ∀ v : HeightOneSpectrum (𝓞 F),
      algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v) ≠ 0)
    {I : HeightOneSpectrum (𝓞 F) → Type*} [∀ v, Fintype (I v)] [∀ v, Nonempty (I v)]
    (b : ∀ v : HeightOneSpectrum (𝓞 F), I v → v.adicCompletionIntegers F)
    (hI : ∀ v ∉ S, Fintype.card (I v) = Ideal.absNorm v.asIdeal)
    (hsys : ∀ v ∉ S,
      HeckeIntegralSeam.IsHeckeCosetSystem
        (levelOne (𝓞 F) F Φ.level ⊓ finiteAdelicGL2Subgroup F) (heckeGen (𝓞 F) F v)
        (fun i : Option (I v) => i.elim
          (placeEmbed F v (repInf
            (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v)))
          (fun j => placeEmbed F v (repSome
            (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v)
            (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (b v j))))))
    (hHecke : ∀ v ∉ S,
      IsHeckeCosetEigenfunctionAt F (levelOne (𝓞 F) F Φ.level ⊓ finiteAdelicGL2Subgroup F)
        (heckeGen (𝓞 F) F v) v (rightConv F φ f) (Φ.a v))
    (hcentral : ∀ v ∉ S, ∀ g : AdelicGL2 (𝓞 F) F,
      rightConv F φ f (centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 F) F v)) * g)
        = Φ.toRawCentral.b v * rightConv F φ f g)
    (hnormU : ∀ u : (AdeleRing (𝓞 F) F)ˣ,
      (u : AdeleRing (𝓞 F) F).1 = 1 →
      (∀ v ∈ S, (u : AdeleRing (𝓞 F) F).2 v = 1) →
      finitePartUnits (𝓞 F) F u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F →
      ideleNorm F u = 1)
    (g₀ : AdelicGL2 (𝓞 F) F)
    (hg₀ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∀ i j : Fin 2,
      ((g₀ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v =
        ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v)
    (B : AdeleRing (𝓞 F) F → ℂ) (hB : B ∈ NumberField.AdelicFourier.schwartzBruhat F)
    (hBstd : ∃ (Bi : (w : InfinitePlace F) → w.Completion → ℂ) (Bf : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ),
      IsFactorizableStandardOutside B S Bi Bf)
    (ΦB : AdelicGL2 (𝓞 F) F → ℂ)
    (hΦB : ∀ h : AdelicGL2 (𝓞 F) F, ΦB h = (letI := adeleBorel (𝓞 F) F
        ∫ x, B x * rightConv F φ (fun y => f (g₀⁻¹ * y)) (h * unipotentGL2 x) ∂(adelicAddHaar (𝓞 F) F))) :
    (∀ v ∉ S, ∀ (x : v.adicCompletion F) (g : GL (Fin 2) (AdeleRing (𝓞 F) F)),
      whittakerCoefficient F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ ΦB 1 (placeEmbed F v (unipotent x) * g) = ψv v x * whittakerCoefficient F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ ΦB 1 g) ∧
    (∀ v ∉ S, ∀ (r : v.adicCompletionIntegers F) (g : GL (Fin 2) (AdeleRing (𝓞 F) F)),
      whittakerCoefficient F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ ΦB 1 (g * placeEmbed F v (unipotent
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r))) = whittakerCoefficient F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ ΦB 1 g) ∧
    (∀ v ∉ S, ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F),
      (∑ i, whittakerCoefficient F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ ΦB 1 (g * placeEmbed F v (repSome
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v)
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (b v i))))) +
        whittakerCoefficient F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ ΦB 1 (g * placeEmbed F v (repInf
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v))) =
        Φ.a v * whittakerCoefficient F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ ΦB 1 g) ∧
    (∀ v ∉ S, ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F),
      whittakerCoefficient F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ ΦB 1 (g * placeEmbed F v (scalarPi
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v))) =
        Φ.toRawCentral.b v * whittakerCoefficient F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ ΦB 1 g) ∧
    (∀ w : (AdeleRing (𝓞 F) F)ˣ,
      (w : AdeleRing (𝓞 F) F).1 = 1 →
      (∀ v ∈ S, (w : AdeleRing (𝓞 F) F).2 v = 1) →
      finitePartUnits (𝓞 F) F w ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F →
      ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F), whittakerCoefficient F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ ΦB 1 (g * diagOne w) = whittakerCoefficient F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ ΦB 1 g) := by sorry
