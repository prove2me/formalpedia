-- Prove2me | Theorems.Thm_BudgetedAffine_Disjoint_lemma_4_2
-- name    : BudgetedAffine.Disjoint.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T21:18:22.036983+00:00
-- url     : https://prove2.me/theorems/cfa844cc-0f8f-4d5b-a6d2-0ba2653ef0fd
-- title:
--   Lemma 4.2 — the affine solution (4.7) is feasible
-- statement:
--   In the setting of Lemma 4.1 (optimal $(x^*,y^*)$ with value $\mathrm{OPT}$, an online covering algorithm $\mathcal A$ for $\tilde B$ with ratio $\rho$, a run $a_1,\dots,a_L$ of Algorithm 1), let $\mathcal I=\bigcup_\ell\mathcal I_\ell$ be the threshold set of Sec. 4.2, let $v_i$ be an optimal solution of $z(e_i)$ for each $i\in\mathcal I$, and let $(x_{Sta},y_{Sta})$ be an optimal solution of the static problem (4.6). Then the affine solution (4.7)
--   $$x=x_{Sta},\qquad y(h)=\sum_{i\in\mathcal I}\alpha_ih_iv_i+y_{Sta}$$
--   is feasible for the adjustable problem (1.1) over the disjoint constrained budgeted set: $x\in\mathcal X$ and, for every $h\in\mathcal U$, $y(h)\ge0$ and $Ax+By(h)\ge h$.
--
--   Together with Lemmas 4.3 and 4.4 this shows that the affine policy's cost bounds $z_{Aff}(\mathcal U)$.
--
--   **Formalization Note** The policy is the explicit affine map $h\mapsto Ph+y_{Sta}$, with $P$ the matrix whose column $i$ is $\alpha_iv_i$ for $i\in\mathcal I$ and $0$ otherwise. Optimal covers $v_i$ are assumed only for $i\in\mathcal I$, the only ones the construction uses (for $i\notin\mathcal I$ an optimal cover need not exist). The hypothesis $c^Tx\ge0$ on $\mathcal X$ is the mission's standing added hypothesis.
-- source:
--   El Housni, Goyal, On the Optimality of Affine Policies for Budgeted Uncertainty Sets, arXiv:1807.00163v2, Lemma 4.2, p. 18

import Mathlib
import Definitions.Def_BudgetedAffine_Disjoint_Model
import Definitions.Def_BudgetedAffine_Disjoint_OnlineCover
import Definitions.Def_BudgetedAffine_Disjoint_Construction

namespace BudgetedAffine.Disjoint

open Matrix

/-- Lemma 4.2: the affine solution (4.7), `x = x_Sta`, `y(h) = P h + y_Sta` with
`P h = y_Lin(h)` and `I = ⋃_ℓ I_ℓ` built from a run of Algorithm 1, is feasible for (1.1) over the
disjoint constrained budgeted set. -/
theorem lemma_4_2 {m n L : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (c d : Fin n → ℝ)
    (X : Set (Fin n → ℝ)) (S : Fin L → Finset (Fin m)) (w : Fin L → Fin m → ℝ)
    (hB : ∀ i j, 0 ≤ B i j) (hc : 0 ≤ c) (hd : 0 ≤ d) (hX : BudgetedAffine.Budget.IsPolyhedral X)
    (hcX : ∀ x ∈ X, 0 ≤ c ⬝ᵥ x) (hS : IsPartition S) (hw : ∀ ℓ i, 0 ≤ w ℓ i ∧ w ℓ i ≤ 1)
    (xs : Fin n → ℝ) (ys : (Fin m → ℝ) → Fin n → ℝ)
    (hopt : BudgetedAffine.Budget.IsOptimalAR A B c d X (disjointBudgetSet S w) xs ys)
    (OPT : ℝ) (hOPT : BudgetedAffine.Budget.zAR A B c d X (disjointBudgetSet S w) = (OPT : EReal))
    (ρ : ℝ) (hρ : 0 ≤ ρ) (alg : OnlineCover (Btil A B xs) d ρ)
    (σ : Fin L ≃ Fin L) (a : Fin L → Finset (Fin m))
    (ha : IsGreedyRun alg w (hatS S A xs) σ a)
    (v : Fin m → Fin n → ℝ)
    (hv : ∀ i ∈ Iset A B d S w xs σ (nuInc alg a), BudgetedAffine.Budget.IsCoverOpt B d (Pi.single i 1) (v i))
    (xSta ySta : Fin n → ℝ)
    (hSta : BudgetedAffine.Budget.IsStaticOpt A B c d X
      (BudgetedAffine.Budget.staRhs (Iset A B d S w xs σ (nuInc alg a)) (BudgetedAffine.Budget.alpha A xs)) xSta ySta) :
    BudgetedAffine.Budget.Feasible A B X (disjointBudgetSet S w) xSta
      (fun h => BudgetedAffine.Budget.linMatrix (Iset A B d S w xs σ (nuInc alg a)) (BudgetedAffine.Budget.alpha A xs) v *ᵥ h + ySta) := by sorry

end BudgetedAffine.Disjoint
