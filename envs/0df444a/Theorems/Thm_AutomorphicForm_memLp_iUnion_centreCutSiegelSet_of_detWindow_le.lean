-- Prove2me | Theorems.Thm_AutomorphicForm_memLp_iUnion_centreCutSiegelSet_of_detWindow_le
-- name    : AutomorphicForm.memLp_iUnion_centreCutSiegelSet_of_detWindow_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/df353f6d-c4d2-5dd5-bb9b-f99ff71c5ead
-- title:
--   Extending the determinant window of an L² automorphic function
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2,d_p$ be real numbers, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$, with $0<d_p$, $d_p<d_2$ and $d_1\le d_p$. For real parameters $a\le b$ the set `centreCutSiegelSet F c u a b` consists of those $g\in\mathrm{GL}_2(\mathbb{A}_F)$ whose finite component lies in `finiteIntegralGL2`, i.e. in the full level-zero subgroup `finiteLevelZero (𝓞 F) F ⊤` of $\mathrm{GL}_2$ over the finite adeles, and whose component $g_w$ at each infinite place $w$ satisfies $c\le\lVert\det g_w\rVert/\mathrm{rowNormSq}(g_w)$, $\mathrm{topNormSq}(g_w)/\mathrm{rowNormSq}(g_w)-(\lVert\det g_w\rVert/\mathrm{rowNormSq}(g_w))^2\le u^2$, and $\lVert\det g_w\rVert\in[a,b]$. Let $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ be almost everywhere strongly measurable for the Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_F)$ (taken with its Borel $\sigma$-algebra), and let $\omega:\mathbb{A}_F^\times\to\mathbb{C}^\times$ be a group homomorphism with $\varphi(z\cdot g)=\omega(z)\varphi(g)$ for all ideles $z$, where $z$ acts through the central scalar embedding. Assume that if $d_1\le 0$ then $\omega$ is contracting at each infinite place, in the sense that $\lvert\omega(\iota_w(a))\rvert<1$ for every $w$ and every unit $a$ of $F_w$ with $\lVert a\rVert<1$, $\iota_w(a)$ denoting the idele equal to $a$ at $w$ and to $1$ elsewhere. If $\varphi$ is square-integrable for Haar measure restricted to $\bigcup_{x\in T}\;\mathrm{centreCutSiegelSet}\,F\,c\,u\,d_p\,d_2\cdot x$, then it is square-integrable for Haar measure restricted to $\bigcup_{x\in T}\;\mathrm{centreCutSiegelSet}\,F\,c\,u\,d_1\,d_2\cdot x$.
--
--   This is the window-enlargement step in the reduction theory used to handle square-integrability on centre-cut Siegel sets: it lets the determinant-norm interval $[d_p,d_2]$ at the infinite places be pushed down to $[d_1,d_2]$, possibly reaching or crossing $0$, at the cost of a contraction condition on the central character in that case. It is used in the construction and comparison of cuspidal constituents and in the approximation of such functions by finite sums of translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_memLp_iUnion_centreCutSiegelSet_of_detWindow_le.lean

import Definitions.Def_AutomorphicForm_CentreCutSiegelSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar AutomorphicForm AutomorphicForm.WindowedSiegel
  MeasureTheory

theorem AutomorphicForm.memLp_iUnion_centreCutSiegelSet_of_detWindow_le
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ dp : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hdp : 0 < dp) (hdp₂ : dp < d₂) (hd₁ : d₁ ≤ dp)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφm : letI := glBorel (Fin 2) (𝓞 F) F; AEStronglyMeasurable φ (adelicGLHaar (Fin 2) (𝓞 F) F))
    (ω : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hω : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * φ g)
    (hcontr : d₁ ≤ 0 → ∀ (w : InfinitePlace F) (a : (w.Completion)ˣ), ‖(a : w.Completion)‖ < 1 →
      ‖((ω (AdelicVolume.archCentralUnit F w a) : ℂˣ) : ℂ)‖ < 1)
    (hL2 : letI := glBorel (Fin 2) (𝓞 F) F;
      MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u dp d₂))) :
    letI := glBorel (Fin 2) (𝓞 F) F;
    MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) := by sorry
