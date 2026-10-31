-- Prove2me | Theorems.Thm_AubinLipschitz_clarkeDeriv_paramMap_iff
-- name    : AubinLipschitz.clarkeDeriv_paramMap_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:52:04.17976+00:00
-- url     : https://prove2.me/theorems/cab12689-8519-465f-81ac-0f3f4495fac6
-- title:
--   §5, Lemma 1 — the Clarke derivative of $F$ in terms of those of $G$ and $H^{-1}$
-- statement:
--   Let $X,Y$ be finite-dimensional and $F$ the map of (9)–(10), built from $G$ and $H^{-1}$. Let $(x_0,q_0)$ solve
--
--   $$
--   p_0\in G(x_0)+A_0^*q_0,\qquad y_0\in -A_0x_0+H^{-1}(q_0).
--   $$
--
--   Then $(\delta p,\delta y,\delta A)\in CF(x_0,q_0;p_0,y_0,A_0)(\delta x,\delta q)$ if and only if
--
--   1. $\delta p-\delta A^*\cdot q_0\in CG(x_0,p_0-A_0^*q_0)(\delta x)+A_0^*\delta q$, and
--   2. $\delta y+\delta A\cdot x_0\in -A_0\delta x+CH^{-1}(q_0,y_0+A_0x_0)(\delta q)$.
--
--   So the derivative of the whole system is computed block by block.
--
--   Differences from the source:
--   - generalization: G = ∂U and H⁻¹ = ∂V* → arbitrary set-valued G from X to X* and H⁻¹ from Y* to Y; reason: the printed proof uses no property of G and H⁻¹, and the choice G = ∂U, H⁻¹ = ∂V* gives the paper's statement.
-- source:
--   Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, Lemma 1, p.33

import Mathlib
import Definitions.Def_AubinLipschitz_clarkeDeriv
import Definitions.Def_AubinLipschitz_paramMap

namespace AubinLipschitz

/-- Aubin, Lipschitz Behavior of Solutions to Convex Minimization Problems, IIASA WP-81-76 (1981), §5, Lemma 1, p.33: if `(x₀, q₀)` solves (11), `p₀ ∈ G(x₀) + A₀*q₀`,
`y₀ ∈ −A₀x₀ + H⁻¹(q₀)`, then `(δp, δy, δA) ∈ CF(x₀, q₀; p₀, y₀, A₀)(δx, δq)` if and only if
(i) `δp − δA*·q₀ ∈ CG(x₀, p₀ − A₀*q₀)(δx) + A₀*δq` and
(ii) `δy + δA·x₀ ∈ −A₀δx + CH⁻¹(q₀, y₀ + A₀x₀)(δq)`. -/
theorem clarkeDeriv_paramMap_iff {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (G : X → Set (StrongDual ℝ X)) (Hinv : StrongDual ℝ Y → Set Y) (A₀ : X →L[ℝ] Y)
    (p₀ : StrongDual ℝ X) (y₀ : Y) (x₀ : X) (q₀ : StrongDual ℝ Y)
    (h₁ : ∃ g ∈ G x₀, p₀ = g + q₀.comp A₀) (h₂ : ∃ h ∈ Hinv q₀, y₀ = -(A₀ x₀) + h)
    (δx : X) (δq : StrongDual ℝ Y) (δp : StrongDual ℝ X) (δy : Y) (δA : X →L[ℝ] Y) :
    (δp, δy, δA) ∈ clarkeDeriv (paramMap G Hinv) (x₀, q₀) (p₀, y₀, A₀) (δx, δq) ↔
      (∃ a ∈ clarkeDeriv G x₀ (p₀ - q₀.comp A₀) δx, δp - q₀.comp δA = a + δq.comp A₀) ∧
      ∃ b ∈ clarkeDeriv Hinv q₀ (y₀ + A₀ x₀) δq, δy + δA x₀ = -(A₀ δx) + b := by sorry

end AubinLipschitz
