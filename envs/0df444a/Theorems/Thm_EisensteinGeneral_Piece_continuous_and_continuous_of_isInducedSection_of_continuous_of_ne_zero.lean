-- Prove2me | Theorems.Thm_EisensteinGeneral_Piece_continuous_and_continuous_of_isInducedSection_of_continuous_of_ne_zero
-- name    : EisensteinGeneral.Piece.continuous_and_continuous_of_isInducedSection_of_continuous_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/bdcf91b4-9027-5733-8480-f7f3d67af2d2
-- title:
--   Continuity of the inducing characters of a non-vanishing section
-- statement:
--   Let $F$ be a number field, with adele ring $\mathbf{A}_F$ of $\mathcal{O}_F$ in $F$ and idele group $\mathbf{A}_F^\times$. Let $\alpha : \mathbf{A}_F^\times \to \mathbb{R}^\times$ be a group homomorphism whose values are all positive and which is continuous as a real-valued function, let $\mu, \nu : \mathbf{A}_F^\times \to \mathbb{C}^\times$ be group homomorphisms, let $s_0 \in \mathbb{C}$, and let $\varphi_0$ be a complex-valued function on $\mathrm{GL}_2(\mathbf{A}_F)$. Assume $\varphi_0$ is an induced section for the pair of characters $\eta_1 = \mu \cdot \alpha^{s_0 + 1/2}$ and $\eta_2 = \nu \cdot \alpha^{-(s_0+1/2)}$, where $\alpha^{s}(x) = (\alpha(x))^{s}$ is the complex power of the positive real $\alpha(x)$; that is, for every $b \in \mathrm{GL}_2(\mathbf{A}_F)$ whose lower-left entry vanishes and every $g \in \mathrm{GL}_2(\mathbf{A}_F)$ one has $\varphi_0(bg) = \eta_1(b_{00})\,\eta_2(b_{11})\,\varphi_0(g)$, the diagonal entries $b_{00}, b_{11}$ being units of $\mathbf{A}_F$. Assume further that $\varphi_0$ is continuous and that $\varphi_0(g_0) \neq 0$ for some $g_0$. Then $\mu$ and $\nu$ are continuous.
--
--   This is the standard observation that a continuous induced section of a principal series which is not identically zero forces its inducing quasi-characters to be continuous: one tests the transformation law on the diagonal tori $\mathrm{diag}(t,1)$ and $\mathrm{diag}(1,t)$ at a point where the section does not vanish. It is used in the construction of the Eisenstein pieces, in the results on meromorphic continuation of the Weyl intertwining integral and on the Whittaker expansion of the Bruhat–Eisenstein series with its partial Euler product.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinGeneral_Piece_continuous_and_continuous_of_isInducedSection_of_continuous_of_ne_zero.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm

theorem EisensteinGeneral.Piece.continuous_and_continuous_of_isInducedSection_of_continuous_of_ne_zero
    (F : Type) [Field F]
    [NumberField F] (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((α x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s₀ : ℂ) (φ₀ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ₀ : IsInducedSection (𝓞 F) F (etaFst μ α hα s₀) (etaSnd ν α hα s₀) φ₀) (hφ₀c : Continuous φ₀)
    (g₀ : AdelicGL2 (𝓞 F) F) (hne : φ₀ g₀ ≠ 0) :
    Continuous μ ∧ Continuous ν := by sorry
