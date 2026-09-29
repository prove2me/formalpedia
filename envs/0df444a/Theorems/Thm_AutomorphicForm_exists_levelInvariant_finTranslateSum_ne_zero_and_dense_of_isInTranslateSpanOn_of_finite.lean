-- Prove2me | Theorems.Thm_AutomorphicForm_exists_levelInvariant_finTranslateSum_ne_zero_and_dense_of_isInTranslateSpanOn_of_finite
-- name    : AutomorphicForm.exists_levelInvariant_finTranslateSum_ne_zero_and_dense_of_isInTranslateSpanOn_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/0033515a-3a92-57b8-a211-498c482e1fa6
-- title:
--   Nonzero level combinations of translates, and their mean-square density
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real with $0<c$, $0<d_1<d_2$, let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$, and put $D=\bigcup_{x\in T}\{s\,x : s\in\mathfrak S\}$, where $\mathfrak S$ is the centre-cut Siegel set `centreCutSiegelSet F c u d₁ d₂` (finite part integral, all archimedean local heights $\ge c$, all window squares $\le u^2$, all archimedean determinant norms in $[d_1,d_2]$). Assume $D$ covers modulo the centre, i.e. every $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g\,z\in D$, and that $\{\gamma\in\mathrm{GL}_2(F) : \gamma s\in\mathfrak S\text{ for some } s\in\mathfrak S\}$ is finite. Let $\xi$ be a character of the full idele unit group (the centre $Z=\top$ of the pins `productionPinsOf` built from $D$, the level groups $N\mapsto$ `levelOne` $N\sqcap$ `finiteAdelicGL2Subgroup`, the Hecke generators, and `adelicBox`), let $N\neq 0$ be an ideal of $\mathcal O_F$, and let $\varphi,\varphi'$ be continuous functions on $\mathrm{GL}_2(\mathbb{A}_F)$ that are smooth automorphic at these pins for $\xi$ (automorphic with the `adelicGLHaar` integrability condition on $D$, and smooth vectors for right translation by the kernel of `glArch`). Assume $\varphi$ is right invariant under $U=\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, that $\varphi'$ is not identically zero, and that $\varphi'$ lies in the mean-square translate span of $\varphi$ on $D$: for every $\varepsilon>0$ there are a finite set $s$ and coefficients $l$ with $\int_D\|\varphi'(y)-\sum_{h\in s}l(h)\varphi(yh)\|^2<\varepsilon$. Call a level combination of $\varphi'$ a finite sum $\Psi=\sum_{h\in t}l(h)\,\varphi'(\cdot\,h)$ with all $h\in t$ in $\ker(\mathrm{glArch})$ and $\Psi$ right $U$-invariant. The conclusion is twofold: first, some level combination of $\varphi'$ is not identically zero; second, for every $\varepsilon>0$ in $[0,\infty]$ there are finitely many level combinations $\Psi_1,\dots,\Psi_n$ of $\varphi'$ and elements $x_1,\dots,x_n\in\mathrm{GL}_2(\mathbb{A}_F)$ with $\int_D\|\varphi'(y)-\sum_{i}\Psi_i(y\,x_i)\|^2\,d(\mathrm{adelicGLHaar})<\varepsilon$.
--
--   This is the harmonic-analysis step which converts a witness $\varphi'$ in the closed mean-square translate span of a vector of level $N$ into functions of level $N$ manufactured from $\varphi'$ itself by finite-adelic translation and averaging, together with the statement that these level combinations still approximate $\varphi'$ in mean square on the covering window. It is used in the reconstruction of a cuspidal realisation at an anchor, where properties of $\varphi'$ stable under mean-square limits of translates are transferred to functions of the prescribed level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_levelInvariant_finTranslateSum_ne_zero_and_dense_of_isInTranslateSpanOn_of_finite.lean

import Definitions.Def_AutomorphicForm_TranslateSpanOccurrence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

theorem AutomorphicForm.exists_levelInvariant_finTranslateSum_ne_zero_and_dense_of_isInTranslateSpanOn_of_finite
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (hfin : Set.Finite {γ : Matrix.GeneralLinearGroup (Fin 2) F |
      ∃ s ∈ centreCutSiegelSet F c u d₁ d₂, globalPoints (𝓞 F) F γ * s ∈ centreCutSiegelSet F c u d₁ d₂})
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (φ φ' : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) (hφ' : Continuous φ')
    (hφa : IsSmoothAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ)
    (hφ'a : IsSmoothAutomorphicFnAt F
      (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ φ')
    (hφU : ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F,
      φ (g * k) = φ g)
    (hne : ∃ g, φ' g ≠ 0)
    (hspan : IsInTranslateSpanOn F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) φ φ') :
    (∃ (t : Finset (AdelicGL2 (𝓞 F) F)) (l : AdelicGL2 (𝓞 F) F → ℂ),
        (∀ h ∈ t, h ∈ finiteAdelicGL2Subgroup F) ∧
        (∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F,
          ∑ h ∈ t, l h * φ' (g * k * h) = ∑ h ∈ t, l h * φ' (g * h)) ∧
        ∃ g, ∑ h ∈ t, l h * φ' (g * h) ≠ 0) ∧
    (∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (n : ℕ) (t : Fin n → Finset (AdelicGL2 (𝓞 F) F)) (l : Fin n → AdelicGL2 (𝓞 F) F → ℂ)
        (x : Fin n → AdelicGL2 (𝓞 F) F),
        (∀ i, ∀ h ∈ t i, h ∈ finiteAdelicGL2Subgroup F) ∧
        (∀ i, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F,
          ∑ h ∈ t i, l i h * φ' (g * k * h) = ∑ h ∈ t i, l i h * φ' (g * h)) ∧
        ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂,
            (‖φ' y - ∑ i, ∑ h ∈ t i, l i h * φ' (y * x i * h)‖₊ : ℝ≥0∞) ^ 2
              ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ε) := by sorry
