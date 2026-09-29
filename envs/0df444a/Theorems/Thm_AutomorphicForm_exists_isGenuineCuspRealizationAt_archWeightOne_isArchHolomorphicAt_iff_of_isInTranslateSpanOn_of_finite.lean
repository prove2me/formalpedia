-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isGenuineCuspRealizationAt_archWeightOne_isArchHolomorphicAt_iff_of_isInTranslateSpanOn_of_finite
-- name    : AutomorphicForm.exists_isGenuineCuspRealizationAt_archWeightOne_isArchHolomorphicAt_iff_of_isInTranslateSpanOn_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/4cdc8119-8046-56e5-acd1-299de0bd511c
-- title:
--   Weight-one realization of Theta from a translate-span witness
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $0<c$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb A_F)$. Write $\mathfrak S$ for `centreCutSiegelSet F c u d₁ d₂`, the set of $g$ whose finite part lies in `finiteIntegralGL2`, with $c\le$ `localHeight` and `xWindowSq` $\le u^2$ of the component of $g$ at every infinite place, and with `archDetNorm` at every infinite place in $[d_1,d_2]$; put $D=\bigcup_{x\in T}\mathfrak S x$. Assume $D$ covers modulo centre, i.e. every $g$ satisfies $\gamma g z\in D$ for some $\gamma\in\mathrm{GL}_2(F)$ and some central adelic scalar $z$; assume also that $\{\gamma\in\mathrm{GL}_2(F):\exists s\in\mathfrak S,\ \gamma s\in\mathfrak S\}$ is finite. All realizations are taken at the pins `productionPinsOf` over $D$: Haar measure on $\mathrm{GL}_2(\mathbb A_F)$ for the Borel structure, $Z=\top$, level groups $N\mapsto$ `levelOne`$(N)\sqcap$`finiteAdelicGL2Subgroup`, Hecke generators `heckeGen`$(v)$, and additive adelic Haar measure conditioned on `adelicBox`. Let $\Theta,\Theta'$ be complex Hecke eigensystems over $F$ (a nonzero level ideal together with families $a,b$ indexed by the finite places), and let $\Theta.$`toRawCentral` be $\Theta$ with $b_v$ replaced by $b_v$ divided by the absolute norm of $v$. Let $R$, respectively $R'$, be a `SmoothCuspRealizationAt` of $\Theta.$`toRawCentral`, respectively $\Theta'.$`toRawCentral` — a function on $\mathrm{GL}_2(\mathbb A_F)$, not identically zero, with a central character on $Z$, smooth cuspidal automorphic, invariant under the level group attached to the eigensystem's level, and with Hecke eigenvalue $a_v$ and central eigenvalue $b_v$ outside a finite exceptional set of places — and assume both are continuous (`IsGenuineCuspRealizationAt`). Assume $\Theta'$ agrees with $\Theta$ in both $a$ and $b$ outside a finite set of finite places; assume $R'.$`toFun` lies in the mean-square translate span of $R.$`toFun` on $D$, i.e. for every $\varepsilon>0$ there are a finite set $s$ of adelic matrices and coefficients $l$ with $\int_D\lVert R'(y)-\sum_{h\in s}l(h)R(yh)\rVert^2\,dy<\varepsilon$ for Haar measure. Finally, let $w$ be a real infinite place of $F$ and assume the predicate `HasArchCharacterAt₀` holds for $R'.$`toFun` with the weight-one character `archWeightOneAt hw` at $w$. The conclusion is that there exists a `SmoothCuspRealizationAt` $R_1$ of $\Theta.$`toRawCentral` at these same pins which is continuous, satisfies the same weight-one archimedean character condition at $w$, and is holomorphic at $w$ in the sense of `IsArchHolomorphicAt` (for every $g$, the function $z\mapsto (\operatorname{Im}z)^{-1}R_1(g\cdot\iota_w(\text{Iwasawa section of }z))$ is differentiable on the upper half-plane) if and only if $R'.$`toFun` is.
--
--   This is the outward direction of the archimedean dictionary at weight one: a weight-one witness $R'$ for an eigensystem agreeing with $\Theta$ away from finitely many places, lying in the mean-square translate span of an anchor realization $R$ of $\Theta$ over a covering union of centre-cut Siegel translates, is converted into a realization of $\Theta$ itself at the anchor's level that carries the weight-one character and is holomorphic exactly when the witness is. It feeds the Langlands–Tunnell step of the project, where a holomorphic weight-one realization is produced from a formal base change datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isGenuineCuspRealizationAt_archWeightOne_isArchHolomorphicAt_iff_of_isInTranslateSpanOn_of_finite.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering NumberField.InfinitePlace

theorem AutomorphicForm.exists_isGenuineCuspRealizationAt_archWeightOne_isArchHolomorphicAt_iff_of_isInTranslateSpanOn_of_finite
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (hfin : Set.Finite {γ : Matrix.GeneralLinearGroup (Fin 2) F |
      ∃ s ∈ centreCutSiegelSet F c u d₁ d₂, globalPoints (𝓞 F) F γ * s ∈ centreCutSiegelSet F c u d₁ d₂})
    (Θ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ.toRawCentral R)
    (Θ' : HeckeEigensystem F ℂ) (hΘ' : Θ'.AgreesAwayFromFinite Θ)
    (R' : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ'.toRawCentral)
    (hR' : IsGenuineCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ'.toRawCentral R')
    (hspan : IsInTranslateSpanOn F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) R.toFun R'.toFun)
    (w : InfinitePlace F) (hw : w.IsReal)
    (hR'w : HasArchCharacterAt₀ F w (archWeightOneAt hw) R'.toFun) :
    ∃ R₁ : SmoothCuspRealizationAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
      Θ.toRawCentral,
      IsGenuineCuspRealizationAt F
        (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
          (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F))
        Θ.toRawCentral R₁ ∧
      HasArchCharacterAt₀ F w (archWeightOneAt hw) R₁.toFun ∧
      (IsArchHolomorphicAt w hw R₁.toFun ↔ IsArchHolomorphicAt w hw R'.toFun) := by sorry
