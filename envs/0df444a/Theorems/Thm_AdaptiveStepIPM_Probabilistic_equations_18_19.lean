-- Prove2me | Theorems.Thm_AdaptiveStepIPM_Probabilistic_equations_18_19
-- name    : AdaptiveStepIPM.Probabilistic.equations_18_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:21:15.32014+00:00
-- url     : https://prove2.me/theorems/1bcba589-c6dd-43ea-a353-000b7a986ba9
-- title:
--   Equations (18)–(19) — componentwise projection bound
-- statement:
--   Let $g,w\in\mathbb R^n$, $-1\le\zeta\le1$, and $\eta=\sqrt{1-\zeta^2}$. Put $p=(1+\zeta)g+\eta w$ and $q=(1-\zeta)g-\eta w$. In every coordinate $j$,
--
--   $$
--   p_jq_j=\eta^2g_j^2-2\zeta\eta g_jw_j-\eta^2w_j^2
--   =-w_j^2+(\eta g_j-\zeta w_j)^2
--   \ge-\|w\|_\infty^2.
--   $$
--
--   Consequently $\|Pq\|^-_\infty\le\|w\|_\infty^2$. For $w=Hv$ this is the deterministic step connecting Lemma 6 to Theorem 5.
--
--   **Formalization Note** Here $P=\operatorname{diag}(p)$. The equivalent hypothesis $\zeta^2\le1$ gives the real square root its intended domain.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 15, Eqs. (18)–(19); https://doi.org/10.1287/moor.18.4.964

import Definitions.Def_AdaptiveStepIPM_Probabilistic_Model

open MeasureTheory ProbabilityTheory Filter

namespace AdaptiveStepIPM.Probabilistic

/-- The componentwise identity (18) and lower bound (19). -/
theorem equations_18_19 {n : ℕ} (g w : EuclideanSpace ℝ (Fin n))
    (ζ : ℝ) (hζ : ζ ^ 2 ≤ 1) :
    let η := Real.sqrt (1 - ζ ^ 2)
    let p₀ : Fin n → ℝ := fun j => (1 + ζ) * g j + η * w j
    let q₀ : Fin n → ℝ := fun j => (1 - ζ) * g j - η * w j
    (∀ j : Fin n,
      p₀ j * q₀ j = η ^ 2 * (g j) ^ 2 - 2 * ζ * η * g j * w j - η ^ 2 * (w j) ^ 2 ∧
      p₀ j * q₀ j = -(w j) ^ 2 + (η * g j - ζ * w j) ^ 2 ∧
      -(supNorm w) ^ 2 ≤ p₀ j * q₀ j) ∧
    negSupNorm (fun j => p₀ j * q₀ j) ≤ (supNorm w) ^ 2 := by sorry

end AdaptiveStepIPM.Probabilistic
