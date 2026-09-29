-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_setLIntegral_iUnion_centreCutSiegelSet_le_mul_of_coversModCentre_of_forall_ncard_le
-- name    : AutomorphicForm.exists_forall_setLIntegral_iUnion_centreCutSiegelSet_le_mul_of_coversModCentre_of_forall_ncard_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/0d68c61b-48d4-5bae-aa07-0e292e564023
-- title:
--   Window-to-window L² domination between centre-cut Siegel sets
-- statement:
--   Let $F$ be a number field and write $G = \mathrm{GL}_2(\mathbb{A}_F)$ for `AdelicGL2 (𝓞 F) F`. For real parameters $c,u,d_1,d_2$ and a finite set $T \subseteq G$ put $D = \bigcup_{x \in T} \mathfrak{S}(c,u,d_1,d_2)\,x$, where $\mathfrak{S}(c,u,d_1,d_2) =$ `centreCutSiegelSet F c u d₁ d₂` consists of those $g$ whose finite part lies in `finiteIntegralGL2 (𝓞 F) F` and which satisfy, at every infinite place $w$ of $F$, the bounds $c \le \lVert \det \rVert / \mathrm{rowNormSq}$, $\mathrm{topNormSq}/\mathrm{rowNormSq} - (\lVert \det \rVert/\mathrm{rowNormSq})^2 \le u^2$ and $\lVert \det \rVert_w \in [d_1,d_2]$ for the $w$-component. Assume $d_1 < d_2$ and that $D$ covers modulo the centre: every $g \in G$ admits $\gamma \in \mathrm{GL}_2(F)$ and an idele $z$ with $\gamma g \cdot z I \in D$. Let $c',u',d_1',d_2'$ and a finite $T' \subseteq G$ give a second such union $D'$, with $0 < c'$, $0 < d_1' < d_2'$, and assume uniform multiplicity: there is $M \in \mathbb{N}$ such that for every $h \in G$ the set of $\gamma \in \mathrm{GL}_2(F)$ with $\gamma h \in D'$ is finite of cardinality at most $M$. Let $\xi$ be a homomorphism from the full idele unit group to $\mathbb{C}^{\times}$. Then there is a finite $C \in \overline{\mathbb{R}}_{\ge 0}$ such that for every continuous $\varphi : G \to \mathbb{C}$ which is left $\mathrm{GL}_2(F)$-invariant and satisfies $\varphi(zI \cdot g) = \xi(z)\varphi(g)$, one has $\int^{-}_{D'} \lVert\varphi\rVert^2 \le C \int^{-}_{D} \lVert\varphi\rVert^2$ for the Haar measure `adelicGLHaar (Fin 2) (𝓞 F) F` on the Borel structure `glBorel`.
--
--   This is the comparison principle that Siegel sets belonging to a covering family dominate one another in $L^2$: the square mass of an automorphic function on one centre-cut Siegel window is bounded by a constant multiple of its mass on any window that covers modulo the centre. It feeds the construction of smooth cuspidal realisations, being used by [`AutomorphicForm.exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_of_coversModCentre`](thm.html#AutomorphicForm.exists_smoothCuspRealizationAt_productionPinsGeneral_toFun_eq_of_coversModCentre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_setLIntegral_iUnion_centreCutSiegelSet_le_mul_of_coversModCentre_of_forall_ncard_le.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

theorem AutomorphicForm.exists_forall_setLIntegral_iUnion_centreCutSiegelSet_le_mul_of_coversModCentre_of_forall_ncard_le
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (c' u' d₁' d₂' : ℝ) (T' : Finset (AdelicGL2 (𝓞 F) F)) (hc' : 0 < c') (hd₁' : 0 < d₁') (hd' : d₁' < d₂')
    (hmult : ∃ M : ℕ, ∀ h : AdelicGL2 (𝓞 F) F,
      {γ : Matrix.GeneralLinearGroup (Fin 2) F |
          globalPoints (𝓞 F) F γ * h ∈ ⋃ x ∈ T', (· * x) '' centreCutSiegelSet F c' u' d₁' d₂'}.Finite ∧
        {γ : Matrix.GeneralLinearGroup (Fin 2) F |
          globalPoints (𝓞 F) F γ * h ∈ ⋃ x ∈ T', (· * x) '' centreCutSiegelSet F c' u' d₁' d₂'}.ncard ≤ M)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ → IsLsXiFunction (𝓞 F) F ⊤ ξ φ →
      @lintegral _ (glBorel (Fin 2) (𝓞 F) F)
          ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T', (· * x) '' centreCutSiegelSet F c' u' d₁' d₂'))
          (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) ≤
        C * @lintegral _ (glBorel (Fin 2) (𝓞 F) F)
          ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
          (fun y => (‖φ y‖₊ : ℝ≥0∞) ^ 2) := by sorry
