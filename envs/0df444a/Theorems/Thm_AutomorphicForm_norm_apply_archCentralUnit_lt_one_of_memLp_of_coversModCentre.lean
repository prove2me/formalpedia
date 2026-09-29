-- Prove2me | Theorems.Thm_AutomorphicForm_norm_apply_archCentralUnit_lt_one_of_memLp_of_coversModCentre
-- name    : AutomorphicForm.norm_apply_archCentralUnit_lt_one_of_memLp_of_coversModCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/b124bf20-aabc-578c-8eea-324f5153a5a3
-- title:
--   Square-integrability forces contracting archimedean central character
-- statement:
--   Let $F$ be a number field, let $c,u,d_1,d_2$ be real numbers with $d_1 \le 0 < d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_F)$ (written `AdelicGL2 (𝓞 F) F`). Put $D = \bigcup_{x \in T} (\,\cdot\, x)\,[\,\mathrm{centreCutSiegelSet}\ F\ c\ u\ d_1\ d_2\,]$, the union of the right translates by the elements of $T$ of the set of $g$ whose finite component lies in the full integral subgroup `finiteIntegralGL2 (𝓞 F) F` and whose archimedean component at each infinite place $w$ satisfies $c \le \lVert\det\rVert/\mathrm{rowNormSq}$, $\mathrm{topNormSq}/\mathrm{rowNormSq} - (\lVert\det\rVert/\mathrm{rowNormSq})^2 \le u^2$, and $\lVert \det \rVert \in [d_1,d_2]$. Assume $D$ covers modulo the centre: every $g$ admits $\gamma \in \mathrm{GL}_2(F)$ and an idele unit $z$ with $\gamma g z \in D$. Let $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be continuous, not identically zero, invariant under left multiplication by the image of $\mathrm{GL}_2(F)$, satisfying $\varphi(z g) = \omega(z)\varphi(g)$ for a homomorphism $\omega : \mathbb{A}_F^\times \to \mathbb{C}^\times$ and central scalars $z$, and square-integrable for the adelic Haar measure `adelicGLHaar` restricted to $D$. Then for every infinite place $w$ and every unit $a$ of the completion $F_w$ with $\lVert a \rVert < 1$, the idele $\mathrm{archCentralUnit}\ F\ w\ a$ having component $a$ at $w$ and $1$ at all other places satisfies $\lvert \omega(\mathrm{archCentralUnit}\ F\ w\ a) \rvert < 1$.
--
--   This is the analytic input of reduction theory which says that square-integrability of a non-zero central-character eigenfunction over a covering Siegel window whose determinant interval reaches $0$ forces the archimedean part of the central character to be strictly contracting, i.e. $\lvert \omega_w \rvert = \lVert \cdot \rVert^{\sigma_w}$ with $\operatorname{Re} \sigma_w > 0$ at every infinite place. It is used to transfer statements about coverings and cuspidal constituents between determinant windows, and is cited in the construction of ample centre-cut Siegel sets and in the comparison of $K$-finite cuspidal submodules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_norm_apply_archCentralUnit_lt_one_of_memLp_of_coversModCentre.lean

import Definitions.Def_AutomorphicForm_SiegelCovering

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar AutomorphicForm AutomorphicForm.WindowedSiegel
  AutomorphicForm.SiegelCovering MeasureTheory

theorem AutomorphicForm.norm_apply_archCentralUnit_lt_one_of_memLp_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hd₁ : d₁ ≤ 0) (hd₂ : 0 < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ) (hφ0 : ∃ g, φ g ≠ 0)
    (hγ : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (ω : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hω : ∀ (z : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F),
      φ (centralScalar (𝓞 F) F z * g) = ((ω z : ℂˣ) : ℂ) * φ g)
    (hL2 : letI := glBorel (Fin 2) (𝓞 F) F;
      MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)))
    (w : InfinitePlace F) (a : (w.Completion)ˣ) (ha : ‖(a : w.Completion)‖ < 1) :
    ‖((ω (AdelicVolume.archCentralUnit F w a) : ℂˣ) : ℂ)‖ < 1 := by sorry
