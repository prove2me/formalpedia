-- Prove2me | Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_unramified_package_rightConv_sum_translate
-- name    : AutomorphicForm.SmoothCuspRealizationAt.unramified_package_rightConv_sum_translate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/92f80e34-bd3b-59b7-a2d7-fc0bfc6be888
-- title:
--   Unramified package at a good place for smoothed translate sums
-- statement:
--   Throughout, $K$ is a number field, $\mathbb{A}$ its adele ring, and $\mathrm{GL}_2(\mathbb{A})$ is written `AdelicGL2 (𝓞 K) K`. Real parameters $c,u,d_1,d_2$ and a finite set $T \subseteq \mathrm{GL}_2(\mathbb{A})$ are fixed, together with a Hecke eigensystem $\Theta$ over $\mathbb{C}$, consisting of a nonzero level ideal $\Theta.\mathrm{level}$ of $\mathcal{O}_K$ and families of scalars $a_v, b_v$ indexed by the finite places. The carrier pins used everywhere in the statement are `productionPinsOf K D U gen (adelicBox K)` with: $D = \bigcup_{x \in T} (\,\cdot\, x)\,[\,\Sigma\,]$, the union of the right translates by the elements of $T$ of the centre-cut Siegel set $\Sigma =$ `centreCutSiegelSet K c u d₁ d₂` (those $g$ whose finite part lies in `finiteIntegralGL2`, with $\mathrm{localHeight} \ge c$ and $\mathrm{xWindowSq} \le u^2$ at every infinite place and with archimedean determinant norms in $[d_1,d_2]$); $U(N) =$ `levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, the level-$N$ congruence subgroup intersected with the kernel of the archimedean projection `glArch`; $\mathrm{gen}(v) =$ `heckeGen (𝓞 K) K v`; and the box `adelicBox K`. These pins carry the Borel $\sigma$-algebra and Haar measure on $\mathrm{GL}_2(\mathbb{A})$, the full idele unit group as central subgroup $Z = \top$, and on $\mathbb{A}$ the Borel $\sigma$-algebra with $\nu$ the additive Haar measure conditioned on `adelicBox K`. Finally, `Θ.toRawCentral` is the eigensystem with the same level and the same $a$, and with $b_v$ replaced by $(\mathrm{N}v)^{-1} b_v$, where $\mathrm{N}v =$ `Ideal.absNorm v.asIdeal`.
--
--   The data is: a realization $R$ of type `SmoothCuspRealizationAt K pins Θ.toRawCentral`, that is, a function $R.\mathrm{toFun} : \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ which is somewhere nonzero, carries a central character $R.\mathrm{centralChar}$ on the full idele unit group, satisfies the smooth cuspidal automorphy condition for these pins, is right invariant under $U(\Theta.\mathrm{level})$, and has a finite exceptional set `R.exceptionalSet` outside which it is a Hecke coset eigenfunction at $v$ for $U(\Theta.\mathrm{level})$ and `heckeGen v` with eigenvalue $a_v$ and satisfies the central relation with eigenvalue $(\mathrm{N}v)^{-1} b_v$; the hypothesis `hR`, which is continuity of $R.\mathrm{toFun}$; the hypothesis `hRlev`, right invariance of $R.\mathrm{toFun}$ under $U(\Theta.\mathrm{level})$, which repeats the level-invariance field of $R$; a function $f : \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ with `hfT` asserting that $f$ is factorizable, i.e. $f(g) = f_\infty(\mathrm{glArch}\,g) \cdot f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ with $f_\infty$ compactly supported and smooth in the matrix entries under the mixed embedding and $f_{\mathrm{fin}}$ locally constant with compact support; and three finite sets $S, S_f, S_\psi$ of finite places with `hSf`, `hSψ` asserting $S_f \subseteq S$ and $S_\psi \subseteq S$.
--
--   The support hypothesis `hfsupp` requires of every $z$ with $f(z) \neq 0$ both that the component at $v$ of the finite part of $z$ lies in `localIntegralSet K v` (matrix and inverse with entries in $\mathcal{O}_v$) for every $v \notin S_f$, and that $z$ factors as $z = z_1 z_2$ with $z_2 \in U(\Theta.\mathrm{level})$ and with $z_1$ commuting with [`UnramifiedWhittaker.placeEmbed K v xv`](def/UnramifiedWhittaker_HeckeRecursion.html#L47) for every $v \notin S_f$ and every $xv \in \mathrm{GL}_2(K_v)$. The hypothesis `hS` requires, for every $v \notin S$, that $v$ does not divide $\Theta.\mathrm{level}$ and that $v \notin R.\mathrm{exceptionalSet}$. The hypothesis `hSψ0` requires, for every $v \notin S_\psi$, that the local component `psiLocal K v` of the standard additive character has `addCharLevel` equal to $0$.
--
--   Further data: a natural number $r$, translates $h : \mathrm{Fin}\,r \to \mathrm{GL}_2(\mathbb{A})$ and coefficients $cs : \mathrm{Fin}\,r \to \mathbb{C}$, subject to `hharch`, that each $h_i$ has trivial archimedean component, and `hhcomm`, that each $h_i$ commutes with `placeEmbed K v xv` for every $v \notin S$ and every $xv \in \mathrm{GL}_2(K_v)$. A function $x : \mathrm{GL}_2(\mathbb{A}) \to \mathbb{C}$ is given together with four hypotheses: `hxsum`, that $x(g) = \sum_i cs_i \cdot (\mathrm{rightConv}\, R.\mathrm{toFun}\, f)(g h_i)$, where $(\mathrm{rightConv}\,\varphi\, f)(g) = \int_{\mathrm{GL}_2(\mathbb{A})} \varphi(g y) f(y)\, dy$ against adelic Haar measure; `hxint`, that for every $\alpha' \in K$ and every $g$ the integrand $t \mapsto x(u(t) g)\,\psi(-(\alpha' t))$ defining the Whittaker coefficient of $x$ with respect to the standard global additive character `stdAddChar K` is $\nu$-integrable; `hxper`, that $x(u(\beta + t) \, hh) = x(u(t)\, hh)$ for all $\beta \in K$, $t \in \mathbb{A}$ and $hh \in \mathrm{GL}_2(\mathbb{A})$, where $u(\cdot) =$ `unipotentGL2`; and `hxZ`, that $x(z \cdot g) = R.\mathrm{centralChar}(z)\, x(g)$ for every idele unit $z$ and every $g$. Finally a finite place $v \notin S$ is fixed.
--
--   The conclusion is a conjunction of two parts. The first part asserts: (a) $x\bigl(g \cdot \mathrm{placeEmbed}_v(k_v)\bigr) = x(g)$ for every $k_v \in \mathrm{GL}_2(\mathcal{O}_v)$, mapped into $\mathrm{GL}_2(K_v)$ by the inclusion $\mathcal{O}_v \to K_v$, and every $g$; and (b) `IsHeckeCosetEigenfunctionAt` holds for $U(\Theta.\mathrm{level})$, the generator `heckeGen v`, the place $v$, the function $x$ and the scalar `Θ.toRawCentral.a v` $= a_v$, i.e. there are $\mathrm{N}v + 1$ representatives forming a Hecke coset system for $U(\Theta.\mathrm{level})$ and `heckeGen v` (each lying in the double coset, jointly covering its $U$-cosets, with pairwise distinct classes) such that the corresponding coset sum of $x$ equals $a_v \cdot x$.
--
--   The second part asserts the existence of an additive character $\psi_v$ of $K_v$ with values in $\mathbb{C}$, an element $\varpi \in \mathcal{O}_v$, a proof $h\pi$ that its image in $K_v$ is nonzero, and a family $b : \mathrm{Fin}(\mathrm{N}v) \to \mathcal{O}_v$, such that, writing $W(g)$ for the Whittaker coefficient `whittakerCoefficient` of $x$ at $\alpha = 1$ and $g$ relative to the above pins and `stdAddChar K`, all of the following hold: $\mathrm{placeEmbed}_v\bigl(\mathrm{diag}(\varpi, 1)\bigr) =$ `heckeGen (𝓞 K) K v`; $\mathrm{Valued.v}(\varpi) = \exp(-1)$, so that $\varpi$ is a uniformizer; $\psi_v$ is trivial on (the image of) $\mathcal{O}_v$; there is some $r \in \mathcal{O}_v$ with $\psi_v(r/\varpi) \neq 1$; for all $x_v \in K_v$ and all $g$, $W\bigl(\mathrm{placeEmbed}_v(u(x_v)) \cdot g\bigr) = \psi_v(x_v) \, W(g)$; for all $k_v \in \mathrm{GL}_2(\mathcal{O}_v)$ and all $g$, $W\bigl(g \cdot \mathrm{placeEmbed}_v(k_v)\bigr) = W(g)$; for all $g$,
--   $$\sum_i W\Bigl(g \cdot \mathrm{placeEmbed}_v\bigl(\begin{smallmatrix} \varpi & b_i \\ 0 & 1\end{smallmatrix}\bigr)\Bigr) + W\Bigl(g \cdot \mathrm{placeEmbed}_v\bigl(\begin{smallmatrix} 1 & 0 \\ 0 & \varpi\end{smallmatrix}\bigr)\Bigr) = a_v \, W(g),$$
--   where the matrices are [`UnramifiedWhittaker.repSome`](def/UnramifiedWhittaker_HeckeRecursion.html#L29) and [`UnramifiedWhittaker.repInf`](def/UnramifiedWhittaker_HeckeRecursion.html#L32); and, for all $g$,
--   $$W\Bigl(g \cdot \mathrm{placeEmbed}_v\bigl(\begin{smallmatrix} \varpi & 0 \\ 0 & \varpi\end{smallmatrix}\bigr)\Bigr) = (\mathrm{N}v)^{-1} b_v \, W(g),$$
--   the scalar on the right being `Θ.toRawCentral.b v` and the matrix [`UnramifiedWhittaker.scalarPi`](def/UnramifiedWhittaker_HeckeRecursion.html#L35).
--
--   This is the unramified package at a good place $v$ for a finite linear combination of right translates of a smoothed cuspidal realization: right $\mathrm{GL}_2(\mathcal{O}_v)$-invariance together with the Hecke coset eigen-relation with eigenvalue $a_v$ for the function itself, and the local Whittaker laws at $v$ (quasi-invariance under the local unipotent by an additive character of level $0$, sphericity, and the Hecke and central recursions) for its first Whittaker coefficient. It feeds the construction of test data in the Rankin–Selberg analysis and the non-vanishing of Whittaker coefficients of smoothed translates at maximal compact elements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_unramified_package_rightConv_sum_translate.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp IsDedekindDomain

theorem AutomorphicForm.SmoothCuspRealizationAt.unramified_package_rightConv_sum_translate
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (Θ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ.toRawCentral R)
    (hRlev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K,
      R.toFun (g * k) = R.toFun g)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hfT : IsFactorizableTestFn K f)
    (S Sf Sψ : Finset (HeightOneSpectrum (𝓞 K))) (hSf : Sf ⊆ S) (hSψ : Sψ ⊆ S)
    (hfsupp : ∀ z : AdelicGL2 (𝓞 K) K, f z ≠ 0 →
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf →
        finComponent (𝓞 K) K v (glFin (𝓞 K) K z) ∈ localIntegralSet K v) ∧
      ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K, z = z₁ * z₂ ∧
        z₂ ∈ levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K ∧
        ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf → ∀ xv : GL (Fin 2) (v.adicCompletion K),
          z₁ * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * z₁)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ¬ v.asIdeal ∣ Θ.level ∧ v ∉ R.exceptionalSet)
    (hSψ0 : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sψ →
      LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K v) = 0)
    (r : ℕ) (h : Fin r → AdelicGL2 (𝓞 K) K) (cs : Fin r → ℂ)
    (hharch : ∀ i, glArch (𝓞 K) K (h i) = 1)
    (hhcomm : ∀ i, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ xv : GL (Fin 2) (v.adicCompletion K),
      h i * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * h i)
    (x : AdelicGL2 (𝓞 K) K → ℂ)
    (hxsum : ∀ g, x g = ∑ i, cs i * rightConv K R.toFun f (g * h i))
    (hxint : ∀ (α' : K) (g : AdelicGL2 (𝓞 K) K), WhittakerCoefficientIntegrable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
      (NumberField.StandardAddChar.stdAddChar K) x α' g)
    (hxper : ∀ (β : K) (uu : AdeleRing (𝓞 K) K) (hh : AdelicGL2 (𝓞 K) K),
      x (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + uu) * hh) = x (unipotentGL2 uu * hh))
    (hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x (centralScalar (𝓞 K) K z * g) = ((R.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x g)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ S) :
    ((∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
        x (g * UnramifiedWhittaker.placeEmbed K v (Matrix.GeneralLinearGroup.map
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = x g) ∧
      IsHeckeCosetEigenfunctionAt K (levelOne (𝓞 K) K Θ.level ⊓ finiteAdelicGL2Subgroup K)
        (heckeGen (𝓞 K) K v) v x (Θ.toRawCentral.a v)) ∧
    ∃ (ψv : AddChar (v.adicCompletion K) ℂ) (ϖ : v.adicCompletionIntegers K)
      (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
      (b : Fin (Ideal.absNorm v.asIdeal) → v.adicCompletionIntegers K),
      UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.diagZ
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ 1) = heckeGen (𝓞 K) K v ∧
      Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ) ∧
      (∀ r : v.adicCompletionIntegers K, ψv (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) = 1) ∧
      (∃ r : v.adicCompletionIntegers K, ψv (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r /
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ≠ 1) ∧
      (∀ (xv : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
        whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 (UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.unipotent xv) * g) =
          ψv xv * whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 g) ∧
      (∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
        whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 (g * UnramifiedWhittaker.placeEmbed K v (Matrix.GeneralLinearGroup.map
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) =
          whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 g) ∧
      (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
        (∑ i, whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.repSome
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b i))))) +
          whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.repInf
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) =
          Θ.toRawCentral.a v * whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 g) ∧
      (∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
        whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 (g * UnramifiedWhittaker.placeEmbed K v (UnramifiedWhittaker.scalarPi
              (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) =
          Θ.toRawCentral.b v * whittakerCoefficient K
            (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1 g) := by sorry
