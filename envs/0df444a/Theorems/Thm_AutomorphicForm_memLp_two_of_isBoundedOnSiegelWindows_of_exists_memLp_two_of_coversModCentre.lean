-- Prove2me | Theorems.Thm_AutomorphicForm_memLp_two_of_isBoundedOnSiegelWindows_of_exists_memLp_two_of_coversModCentre
-- name    : AutomorphicForm.memLp_two_of_isBoundedOnSiegelWindows_of_exists_memLp_two_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/fc1d2e96-f417-5f1a-8258-452be94d1b30
-- title:
--   L²-ness of window-bounded forms on covering centre-cut Siegel windows
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1<d_2$, let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb A_F)$, and put $D=\bigcup_{x\in T}\{g x : g\in \mathfrak S\}$, where $\mathfrak S=\mathtt{centreCutSiegelSet}\,F\,c\,u\,d_1\,d_2$ consists of those $g\in\mathrm{GL}_2(\mathbb A_F)$ whose finite component lies in the integral subgroup `finiteIntegralGL2` and which satisfy, at every infinite place $w$ of $F$, the three archimedean conditions $c\le\mathrm{localHeight}(g_w)=\lVert\det g_w\rVert/\mathrm{rowNormSq}(g_w)$, $\mathrm{xWindowSq}(g_w)=\mathrm{topNormSq}(g_w)/\mathrm{rowNormSq}(g_w)-\mathrm{localHeight}(g_w)^2\le u^2$, and $\lVert\det g_w\rVert\in[d_1,d_2]$. Assume $D$ covers modulo the centre: for every $g$ there are $\gamma\in\mathrm{GL}_2(F)$ and $z\in\mathbb A_F^\times$ with $\gamma g\,z\cdot I\in D$. Fix a homomorphism $\xi$ from the full unit group $\mathbb A_F^\times$ (as the subgroup $\top$) to $\mathbb C^\times$, with no continuity or unitarity assumed. Suppose $\varphi_0:\mathrm{GL}_2(\mathbb A_F)\to\mathbb C$ is continuous, not identically zero, satisfies $\varphi_0(\gamma g)=\varphi_0(g)$ for $\gamma\in\mathrm{GL}_2(F)$ and $\varphi_0(zg)=\xi(z)\varphi_0(g)$ for central $z$, and lies in $L^2$ of the Haar measure `adelicGLHaar` restricted to $D$. Let $\psi$ be continuous, satisfying the same two transformation laws for the same $\xi$, and bounded on every window $\bigcup_{x\in T'}\mathfrak S(c',u',d_1',d_2')x$ with $c'>0$ and $d_1'>0$. Then $\psi$ lies in $L^2$ of the Haar measure restricted to $D$.
--
--   This is the comparison step in the construction of the $L^2$-theory on $\mathrm{GL}_2(\mathbb A_F)$ modulo centre: once one function of central character $\xi$ is known to be square-integrable on a covering centre-cut Siegel window, square-integrability transfers to all continuous functions of that central character that are bounded on the nondegenerate windows, even when the determinant window degenerates ($d_1\le 0$). It is used in the analysis of archimedean weight characters and of cuspidal near-equivalence classes on such windows.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_memLp_two_of_isBoundedOnSiegelWindows_of_exists_memLp_two_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicHaar MeasureTheory AutomorphicForm
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

theorem AutomorphicForm.memLp_two_of_isBoundedOnSiegelWindows_of_exists_memLp_two_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (φ₀ : AdelicGL2 (𝓞 F) F → ℂ) (hφ₀ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ₀) (hφ₀c : Continuous φ₀)
    (hφ₀ne : ∃ g, φ₀ g ≠ 0)
    (hφ₀L2 : @MemLp _ _ (glBorel (Fin 2) (𝓞 F) F) _ _ φ₀ 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)))
    (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψ : IsLsXiFunction (𝓞 F) F ⊤ ξ ψ) (hψc : Continuous ψ)
    (hψb : IsBoundedOnSiegelWindows F ψ) :
    @MemLp _ _ (glBorel (Fin 2) (𝓞 F) F) _ _ ψ 2
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) := by sorry
