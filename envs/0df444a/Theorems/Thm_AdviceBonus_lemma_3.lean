-- Prove2me | Theorems.Thm_AdviceBonus_lemma_3
-- name    : AdviceBonus.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:45:48.401661+00:00
-- url     : https://prove2.me/theorems/4bad220a-3dad-4a51-b7a2-1f9571209135
-- title:
--   Lemma 3 — the equilibrium cutoff $\bar q^A_2$ is the unique solution in $(0,1/2)$ of $q=\tfrac12-2G(q)/g(q)$ (15), and $\bar q^B_2=1-\bar q^A_2$ (corrected: equilibria with $b<w$)
-- statement:
--   Let the posterior distribution satisfy the standing assumptions.
--
--   1. The equation
--   $$
--   q=\frac12-\frac{2G(q)}{g(q)} \qquad(15)
--   $$
--   has exactly one solution $q\in(0,1/2)$.
--   2. For all $p,c\in\mathbb R$ and $w>0$: in a symmetric equilibrium compensation scheme $(f,b)$ with $f>0$ and $0<b<w$, the advice cutoff $\bar q^A_2$ for the second customer after $A$ was recommended to the first lies in $(0,1/2)$ and solves (15), and the cutoff after $B$ was recommended is $\bar q^B_2=1-\bar q^A_2$.
--
--   Equation (15) does not involve $w$: the equilibrium advice pattern is independent of the advisor's liability.
--
--   Differences from the source:
--   - correction: a symmetric equilibrium with f > 0 and b > 0 → a symmetric equilibrium with f > 0 and 0 < b < w (advice to the second customer informative: q̄A2, q̄B2 ∈ (0, 1)); reason: the printed statement is false: for g ≡ 1, p − c = 1, w = 1/5 the scheme (f, b) = (3/5, 3/5) is a symmetric equilibrium (q̄A2 = 0, q̄B2 = 1; in the lock-in region firm A's profit is (1/2 + (T − 9/5)/(2/5))(2 − T) in T = 2f′ + b′, maximal at T = 9/5 with value 1/10, and a fine grid over X finds no better deviation for either firm), yet (14) would give b = 4G(0)/g(0)·w = 0; the proof (p.32) starts from the interior cutoffs 1/2 ∓ b/(2w), and §3 restricts to informative advice (p.10)
--   - reading: "uniquely determined by (15)" → (15) has exactly one solution in (0, 1/2), and the equilibrium cutoff lies in (0, 1/2) and solves (15); reason: the proof on p.35 shows uniqueness on (0, 1/2)
--   - reading: "a symmetric equilibrium" → a symmetric pure Nash equilibrium of the compensation stage at the given price p, strategy set {f ≥ 0, 2f + b ≥ 0}, profits (6); reason: §4 takes p_n = p as given (p.16), and p.8 gives the limited-liability strategy set
--   - reading: q̄1 by (4), no corner convention → clamped to [0, 1]; reason: the convention of footnote 19 for (2) and (3)
--   - reading: density g > 0 on [0, 1], hazard rate increasing on [0, 1] → g continuous and positive on [0, 1], hazard rate weakly increasing on [0, 1); reason: the proof uses the intermediate value theorem (p.35) and the hazard rate is undefined at q = 1
--   - generalization: the model's standing assumption (1) on v_h, v_l and c → not assumed; p and c arbitrary reals; reason: §4 takes p as given and (1) only restricts the customer side; the statement specializes to the source's under (1)
--   - encoding: advisor payoffs include w_l → w_l dropped; reason: it cancels from every cutoff
-- source:
--   Honda–Inderst–Ottaviani, When Liability is Not Enough, SSRN 4125013 (May 2022), Lemma 3, eq. (15), p.17; proof in Appendix A, p.35

import Mathlib
import Definitions.Def_AdviceBonus_Model
import Definitions.Def_AdviceBonus_Equilibrium

namespace AdviceBonus

/-- **Lemma 3**, eq. (15), p.17, with its proof on p.35 (Honda–Inderst–Ottaviani, SSRN 4125013,
May 2022).
1. Equation (15), `q = 1/2 − 2G(q)/g(q)`, has exactly one solution `q ∈ (0, 1/2)`.
2. In a symmetric equilibrium with `f_n = f > 0` and `b_n = b > 0` in which the advice to the second
   customer is informative (`b < w`), the cutoff `q̄^A_2` (2) is that solution, and the cutoff after
   a first sale of B is `q̄^B_2 = 1 − q̄^A_2`.

**Formalization Note** (corrected) `b < w` is added as in Lemma 2: for `g ≡ 1`, `p − c = 1`,
`w = 1/5`, the symmetric equilibrium `(3/5, 3/5)` has `q̄^A_2 = 0 ∉ (0, 1/2)`. -/
theorem lemma_3 (D : Dist) :
    (∃! q : ℝ, q ∈ Set.Ioo (0 : ℝ) (1 / 2) ∧ q = 1 / 2 - 2 * D.G q / D.g q) ∧
    ∀ p c w : ℝ, 0 < w → ∀ f b : ℝ, IsSymEq D p c w (f, b) → 0 < f → 0 < b → b < w →
      q2A w (f, b) (f, b) ∈ Set.Ioo (0 : ℝ) (1 / 2) ∧
      q2A w (f, b) (f, b) = 1 / 2 - 2 * D.G (q2A w (f, b) (f, b)) / D.g (q2A w (f, b) (f, b)) ∧
      q2B w (f, b) (f, b) = 1 - q2A w (f, b) (f, b) := by sorry

end AdviceBonus
