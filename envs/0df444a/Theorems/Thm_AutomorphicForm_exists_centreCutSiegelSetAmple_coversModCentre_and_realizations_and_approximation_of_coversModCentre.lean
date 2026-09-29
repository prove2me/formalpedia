-- Prove2me | Theorems.Thm_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre
-- name    : AutomorphicForm.exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/f2211961-9e54-5e83-bc97-75602fc52bda
-- title:
--   Passage from ample to plain centre-cut Siegel windows
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$ and $c>0$, and let $T$ be a finite set of elements of $\mathrm{GL}_2$ of the adeles of $K$. Assume the approximation hypothesis that every family $x$ of elements $x_w$ of the completions at the infinite places of $K$ admits $\xi$ in the ring of integers with $\|x_w-\xi\|\le u$ for all infinite $w$ simultaneously. Write $D$ for the union over $x\in T$ of the right translates by $x$ of `centreCutSiegelSet K c u d₁ d₂`, the set of $g$ whose finite part is integral, whose local height at each infinite place is at least $c$, whose $x$-window square at each infinite place is at most $u^2$, and whose archimedean determinant norm at each infinite place lies in $[d_1,d_2]$; assume `CoversModCentre K D`, i.e. every adelic $g$ can be moved into $D$ by left multiplication by a global point of $\mathrm{GL}_2(K)$ and right multiplication by a central adelic scalar. Let $\Theta,\Theta'$ be Hecke eigensystems over $K$ with complex coefficients (a nonzero level ideal together with coefficient functions $a,b$ on the finite places) agreeing, in both $a$ and $b$, outside some finite set of finite places. Let $R$ and $R'$ be smooth cusp realizations, at the production pins attached to $D$ with level subgroups $N\mapsto$ `levelOne` intersected with the kernel of the archimedean projection, Hecke generators `heckeGen`, and the adelic box as conditioning set, for the raw central rescalings of $\Theta$ and $\Theta'$ (same level and same $a$, with $b_v$ replaced by $(\mathrm{cNorm}\,v)^{-1}b_v$), and assume both are genuine, i.e. their underlying functions are continuous. Then there exist reals $u'$, $d_1'$ and $\kappa$ with $0<d_1'<d_2$ and $\kappa\ge 1$ such that, writing $D_\kappa$ for the union over $x\in T$ of the right translates by $x$ of `centreCutSiegelSetAmple K c u' d₁' d₂ κ` (the points of the corresponding centre-cut Siegel set whose local heights at any two infinite places differ by at most the factor $\kappa$): $D_\kappa$ again covers modulo global points and the centre; there are genuine smooth cusp realizations at the production pins of $D_\kappa$ for the raw central rescalings of $\Theta$ and of $\Theta'$ whose underlying functions are exactly those of $R$ and $R'$; and approximation transfers from $D_\kappa$ to $D$, namely if for every $\delta>0$ there are a finite set $s$ of adelic matrices and coefficients $l$ with $\int_{D_\kappa}\|R'(y)-\sum_{h\in s}l_h R(yh)\|^2\,d\mu<\delta$ for the adelic Haar measure $\mu$ on $\mathrm{GL}_2$, then for every $\varepsilon>0$ there are such $s$ and $l$ (chosen afresh) with the same integral over $D$ less than $\varepsilon$.
--
--   This is a window-comparison step in the adelic proof of strong multiplicity one for $\mathrm{GL}(2)$ over a number field: it replaces a plain centre-cut Siegel window by an ample one, on which height comparability at the infinite places is available, while keeping the covering property, the realizations and the $L^2$ approximation of $R'$ by right translates of $R$. It is used by [`AutomorphicForm.exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre`](thm.html#AutomorphicForm.exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

theorem
AutomorphicForm.exists_centreCutSiegelSetAmple_coversModCentre_and_realizations_and_approximation_of_coversModCentre
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hc : 0 < c)
    (hu : ∀ x : (w : InfinitePlace K) → w.Completion, ∃ ξ : 𝓞 K, ∀ w : InfinitePlace K,
      ‖x w - algebraMap K w.Completion (ξ : K)‖ ≤ u)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (Θ Θ' : HeckeEigensystem K ℂ)
    (hΘ : Θ.AgreesAwayFromFinite Θ')
    (R : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ.toRawCentral R)
    (R' : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ'.toRawCentral)
    (hR' : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K))
      Θ'.toRawCentral R') :
    ∃ u' d₁' κ : ℝ, 0 < d₁' ∧ d₁' < d₂ ∧ 1 ≤ κ ∧
      CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u' d₁' d₂ κ) ∧
      (∃ Rκ : SmoothCuspRealizationAt K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u' d₁' d₂ κ)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))
          Θ.toRawCentral,
        IsGenuineCuspRealizationAt K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u' d₁' d₂ κ)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))
          Θ.toRawCentral Rκ ∧ Rκ.toFun = R.toFun) ∧
      (∃ R'κ : SmoothCuspRealizationAt K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u' d₁' d₂ κ)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))
          Θ'.toRawCentral,
        IsGenuineCuspRealizationAt K
          (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u' d₁' d₂ κ)
            (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K))
          Θ'.toRawCentral R'κ ∧ R'κ.toFun = R'.toFun) ∧
      ((∀ δ : ℝ≥0∞, 0 < δ →
          ∃ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ),
            ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple K c u' d₁' d₂ κ,
                (‖R'.toFun y - ∑ h ∈ s, l h * R.toFun (y * h)‖₊ : ℝ≥0∞) ^ 2
                  ∂(adelicGLHaar (Fin 2) (𝓞 K) K) < δ) →
        ∀ ε : ℝ≥0∞, 0 < ε →
          ∃ (s : Finset (AdelicGL2 (𝓞 K) K)) (l : AdelicGL2 (𝓞 K) K → ℂ),
            ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
                (‖R'.toFun y - ∑ h ∈ s, l h * R.toFun (y * h)‖₊ : ℝ≥0∞) ^ 2
                  ∂(adelicGLHaar (Fin 2) (𝓞 K) K) < ε) := by sorry
