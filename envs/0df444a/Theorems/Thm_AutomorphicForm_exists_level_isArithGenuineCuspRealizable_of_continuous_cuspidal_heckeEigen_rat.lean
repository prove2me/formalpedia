-- Prove2me | Theorems.Thm_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat
-- name    : AutomorphicForm.exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/1401a1d4-eb61-51bd-8e88-939e1887e774
-- title:
--   Genuine cuspidal realizability of a Hecke eigenfunction over ℚ
-- statement:
--   Fix reals $c,u,d_1,d_2$ with $0<c$, $0<d_1$, $d_1<d_2$, a finite set $T\subset \mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$, functions $a,b$ from the finite places of $\mathbb{Q}$ to $\mathbb{C}$, a finite set $S_1$ of finite places, a character $\xi$ of the idele units, and let $D=\bigcup_{x\in T}(\cdot\,x)[\,\mathrm{centreCutSiegelSet}\ \mathbb{Q}\,c\,u\,d_1\,d_2]$, the union of the right translates by the $x\in T$ of the set of $g$ whose finite part is integral and whose archimedean components satisfy $\mathrm{localHeight}\ge c$, $\mathrm{xWindowSq}\le u^2$ and $\mathrm{archDetNorm}\in[d_1,d_2]$; the pins used throughout are `productionPinsOf` for $D$, the level groups $\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, the generators $\mathrm{heckeGen}(v)$ and the adelic box. Let $h:\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})\to\mathbb{C}$ be continuous, invariant under left translation by $\mathrm{GL}_2(\mathbb{Q})$, satisfying $h(zg)=\xi(z)h(g)$ for scalar ideles $z$, with vanishing constant term along the unipotent family $x\mapsto\begin{pmatrix}1&x\\0&1\end{pmatrix}$ computed against the additive adelic Haar measure conditioned to the adelic box, slowly increasing relative to $\mathrm{adelicHeight}$ on every centre-cut Siegel set with parameters $c',u',d_1',d_2'$ ($0<c'$, $0<d_1'$), and, at each $v\notin S_1$: right invariant under the image of $\mathrm{GL}_2(\mathcal{O}_v)$ in $\mathrm{GL}_2(\mathbb{A}_\mathbb{Q})$ under $\mathrm{localEmbed}$ followed by $\mathrm{finEmbed}$, a `IsHeckeCosetEigenfunctionAt` eigenfunction with eigenvalue $a(v)$ for that subgroup and $\mathrm{heckeGen}(v)$ (there are $\mathrm{N}v+1$ coset representatives with $\sum_i h(g r_i)=a(v)h(g)$), and satisfying $h(\det(\mathrm{heckeGen}(v))\cdot g)=(\mathrm{N}v)^{-1}b(v)h(g)$. If $h\ne 0$ somewhere, then there is a nonzero ideal $N$ of $\mathbb{Z}$ all of whose prime divisors lie in $S_1$ such that the eigensystem with level $N$ and data $a,b$ is `IsArithGenuineCuspRealizable` for these pins: the eigensystem with $b$ replaced by $(\mathrm{N}v)^{-1}b(v)$ admits a `SmoothCuspRealizationAt` term satisfying `IsGenuineCuspRealizationAt`.
--
--   This is the passage from a classically described adelic automorphic function on $\mathrm{GL}_2$ over $\mathbb{Q}$ — continuous, cuspidal, of moderate growth on centre-cut Siegel sets, spherical and Hecke-eigen outside a finite set — to the project's notion of a genuine cuspidal realization of the associated Hecke eigensystem at a suitable level divisible only by places in $S_1$. It is used in the Langlands–Tunnell part of the argument, where cuspidality of the form attached to a cubic induction is established.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_LocalLanglands_LocalHeckeInstance
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp

theorem AutomorphicForm.exists_level_isArithGenuineCuspRealizable_of_continuous_cuspidal_heckeEigen_rat
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 ℚ) ℚ))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (a b : HeightOneSpectrum (𝓞 ℚ) → ℂ) (S₁ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ξ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (h : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hcont : Continuous h)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      h (globalPoints (𝓞 ℚ) ℚ γ * g) = h g)
    (hcentral : ∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      h (centralScalar (𝓞 ℚ) ℚ z * g) = ((ξ z : ℂˣ) : ℂ) * h g)
    (hcusp : @IsCuspidalFn _
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).nS
      _ _
      (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)).ν
      unipotentGL2 h)
    (hgrowth : ∀ c' u' d₁' d₂' : ℝ, 0 < c' → 0 < d₁' →
      IsSlowlyIncreasingOn (centreCutSiegelSet ℚ c' u' d₁' d₂') (NumberField.AdelicHeight.adelicHeight ℚ) h)
    (hsph : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₁ → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      ∀ k ∈ (LocalGL2.integralSubgroup (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)).map
        ((AdelicDock.finEmbed (𝓞 ℚ) ℚ).comp (AdelicDock.localEmbed (𝓞 ℚ) ℚ v)), h (g * k) = h g)
    (hhecke : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₁ →
      IsHeckeCosetEigenfunctionAt ℚ
        ((LocalGL2.integralSubgroup (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)).map
          ((AdelicDock.finEmbed (𝓞 ℚ) ℚ).comp (AdelicDock.localEmbed (𝓞 ℚ) ℚ v)))
        (heckeGen (𝓞 ℚ) ℚ v) v h (a v))
    (hcentre : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S₁ → ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      h (centralScalar (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 ℚ) ℚ v)) * g)
        = (HeckeEigensystem.cNorm v)⁻¹ * b v * h g)
    (hne : ∃ g : AdelicGL2 (𝓞 ℚ) ℚ, h g ≠ 0) :
    ∃ (N : Ideal (𝓞 ℚ)) (hN : N ≠ ⊥), (∀ v : HeightOneSpectrum (𝓞 ℚ), v.asIdeal ∣ N → v ∈ S₁) ∧
      IsArithGenuineCuspRealizable ℚ
        (productionPinsOf ℚ (⋃ x ∈ T, (· * x) '' centreCutSiegelSet ℚ c u d₁ d₂)
          (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ))
        ⟨N, hN, a, b⟩ := by sorry
