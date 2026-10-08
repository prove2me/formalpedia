-- Prove2me | Theorems.Thm_CarbonDoubleCount_Planner_proposition_2
-- name    : CarbonDoubleCount.Planner.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:47:45.971305+00:00
-- url     : https://prove2.me/theorems/02c1b234-001b-449a-8f33-c4da4af3e94d
-- title:
--   Proposition 2, p. 12 — first-best implementation with joint production requires double counting
-- statement:
--   Consider firms whose differentiable profits are concave and decreasing in abatement effort, and processes whose differentiable, convex footprints are decreasing in effort and nonnegative on the feasible box. Let $e^*$ be the unique interior social first best at carbon price $p_S>0$. A binary influence matrix $B$ records which firms have a negative total marginal effect on each process, with the same indicator throughout the feasible effort box. Suppose some process is influenced by at least two firms. Let the social planner's rule be
--   $$
--   h_n(\phi)=p_S\widehat f_n(\phi)+g_n(\phi),
--   \qquad\sum_n g_n(\phi)=0\quad\text{for }\phi\ge0.
--   $$
--   If every $h_n$ is differentiable and componentwise increasing and $e^*$ is a Nash equilibrium when firms choose efforts under $h$, then at the first-best footprint $f(e^*)$ some process $i$ is double-counted:
--   $$
--   \sum_n\frac{\partial h_n}{\partial f_i}(f(e^*))>p_S.
--   $$
--   The result rules out first-best implementation by a differentiable increasing rule whose aggregate marginal charge stays at or below the social carbon price at the first-best footprint.
--
--   **Formalization Note** Equation (5) and transfer balance are required only for nonnegative footprint vectors, as printed. The proof establishes double counting at $f(e^*)$, which implies the paper's existential definition. The influence indicator is interpreted as a constant sign pattern over the effort box, and the paper's sufficiently-large effort bound is pinned to interiority of $e^*$. The paper's "without loss of generality" assumption that every row and column of $B$ sums to at least one, and the strictness of the abatement cost's increase, are not imposed: they are unused, and omitting them only generalizes the statement. The split (5) and the balance of $g$ are kept as hypotheses because the proposition is stated for rules given by (5), even though any rule can be written in that form.
-- source:
--   Caro, Corbett, Tan and Zuidwijk, Double-Counting in Supply Chain Carbon Footprinting, working paper dated December 21, 2012, p. 12, Proposition 2 and pp. 24–25, proof A.1; https://www.anderson.ucla.edu/documents/areas/fac/dotm/bio/pdf_FC16.pdf

import Mathlib
import Definitions.Def_CarbonDoubleCount_Planner_Setting

namespace CarbonDoubleCount.Planner

variable {ι : Type} {act : ι → Type} {κ : Type}
variable [Fintype ι] [DecidableEq ι]
variable [∀ n, Fintype (act n)] [∀ n, DecidableEq (act n)]
variable [Fintype κ] [DecidableEq κ]

/-- Proposition 2: a first-best supporting increasing payment rule double-counts. -/
theorem proposition_2
    (A pS : ℝ) (hA : 0 < A) (hpS : 0 < pS)
    (V : (n : ι) → (act n → ℝ) → ℝ)
    (f : ((n : ι) → act n → ℝ) → κ → ℝ)
    (hVdiff : ∀ n, Differentiable ℝ (V n))
    (hfdiff : ∀ i, Differentiable ℝ (fun e => f e i))
    (hVconc : ∀ n, ConcaveOn ℝ (firmBox A n) (V n))
    (hVanti : ∀ n, AntitoneOn (V n) (firmBox A n))
    (hfconv : ∀ i, ConvexOn ℝ (effortBox A) (fun e => f e i))
    (hfanti : ∀ i, AntitoneOn (fun e => f e i) (effortBox A))
    (hfnonneg : ∀ e ∈ effortBox A, ∀ i, 0 ≤ f e i)
    (B : ι → κ → ℝ)
    (hB01 : ∀ n i, B n i = 0 ∨ B n i = 1)
    (hB : ∀ e ∈ effortBox A, ∀ n i,
      (B n i = 1 ↔ (∑ j, dEff (fun e => f e i) e n j) < 0))
    (estar : (n : ι) → act n → ℝ)
    (hfb : IsFirstBest A V f pS estar)
    (hint : ∀ n j, 0 < estar n j ∧ estar n j < A)
    (huniq : ∀ e ∈ effortBox A, IsFirstBest A V f pS e → e = estar)
    (hjoint : JointProduction B)
    (fhat g h : ι → (κ → ℝ) → ℝ)
    (h5 : ∀ n φ, (∀ i, 0 ≤ φ i) → h n φ = pS * fhat n φ + g n φ)
    (hg : ∀ φ : κ → ℝ, (∀ i, 0 ≤ φ i) → ∑ n, g n φ = 0)
    (hdiff : ∀ n, Differentiable ℝ (h n))
    (hmono : ∀ n, Monotone (h n))
    (hnash : IsNash A V f h estar) :
    DoubleCounts h pS (f estar) := by sorry

end CarbonDoubleCount.Planner
