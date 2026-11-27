-- Prove2me | Theorems.Thm_DROOptimal_Predictor_Supplement_theorem_11
-- name    : DROOptimal.Predictor.Supplement.theorem_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T08:34:17.366815+00:00
-- url     : https://prove2.me/theorems/c1ce769b-f24a-4283-8810-07543920ee83
-- title:
--   Theorem 11, p. 26 — every positive shift is feasible for r ≥ 0; the unshifted pair is preferred to every feasible pair for r > 0
-- statement:
--   Let $X\subseteq\mathbb R^n$ and $\Xi\subseteq\mathbb R^d$ be compact, let $\gamma:X\times\Xi\to\mathbb R$ be jointly continuous, and let $\mathcal P$ be all Borel probability distributions on $\Xi$ with the weak topology. For $r\ge0$, write $\hat c_r$ for the published relative-entropy robust predictor. Fix any quasi-continuous selector $\hat x_r(\mathbb P')\in\operatorname*{argmin}_{x\in X}\hat c_r(x,\mathbb P')$ for every $\mathbb P'\in\mathcal P$.
--
--   Then both assertions hold:
--   $$
--   \forall\epsilon>0:\quad (\hat c_r+\epsilon,\hat x_r)\text{ is feasible in (6)}.
--   $$
--   $$
--   r>0\ \Longrightarrow\ \forall(\hat c,\hat x)\text{ feasible in (6)}:\quad
--   \hat c_r(\hat x_r(\mathbb P'),\mathbb P')\le\hat c(\hat x(\mathbb P'),\mathbb P')\quad\forall\mathbb P'\in\mathcal P.
--   $$
--   Feasibility includes joint continuity of the predictor, quasi-continuity and the argmin property of the selector, and prescription-disappointment rate at most $-r$ under every model. The same $\hat x_r$ is retained for every positive additive constant shift. The second assertion compares unshifted predicted optimal values, and does not assert feasibility of the unshifted pair. This gives the source's essential feasibility and preference guarantee on arbitrary compact continuous scenario domains.
--
--   Differences from the source:
--   - encoding: Compact Euclidean domains X and Xi, all Borel probability models with the weak topology, and jointly continuous cost → Decision and scenario subtypes of EuclideanSpace, IsCompact X, IsCompact Xi, Continuous gamma, and the published Continuous.Dist Xi; reason: These represent exactly the standing assumptions of §2 p. 5 and §5 p. 23; no finite-support restriction or extra nonemptiness premise is imposed
--   - encoding: Any quasi-continuous distributionally robust prescriptor of Definition 7, reused in §5 → An arbitrary function xhat_r with the source neighborhood quasi-continuity and membership in the published argminSet of Continuous.drPredictor for every model realization; reason: This unfolds the source-defined prescriptor; it does not assume either theorem conclusion, selector continuity or selector measurability
--   - encoding: The infinite i.i.d. sampling probability of an event depending only on the first T samples → The published Continuous.sampleProb, the outer probability under the T-fold product measure, zero at T=0; reason: Finite-coordinate events have the same probability; outer probability retains all source-valid quasi-continuous selectors without a new measurability assumption, and the unused T=0 value cannot affect the asymptotic constraint
--   - encoding: Upper logarithmic probability rate at most -r, with log 0 = -infinity → The published DecaysAtRate (ENNReal.ofReal r); reason: For probability sequences and r≥0 this is equivalent to eventual exponential bounds at every nonnegative finite rate below r, including zero probabilities and the automatic r=0 case
--   - encoding: The distributionally robust predictor defined using generalized relative entropy and a supremum over probability models → The published Continuous.drPredictor, cost and relEnt with extended nonnegative KL divergence; reason: Compactness and joint continuity ensure integrability and bounded costs; for r≥0 the entropy ball contains its center, so the real supremum is the intended supremum
--   - reading: Theorem 11 p. 26 says r>0 for preference; the final proof sentence p. 37 says epsilon>0 → The second conclusion requires r>0 and has no epsilon premise; reason: The theorem statement and its separate unshifted conclusion determine the reading; epsilon only belongs to the shifted feasibility clause, so the printed theorem itself needs no correction
-- source:
--   Van Parys, Mohajerin Esfahani & Kuhn, From Data to Decisions: Distributionally Robust Optimization is Optimal, arXiv:1704.04118v3, p. 26, Theorem 11; proof pp. 36–37; standing assumptions §2 p. 5 and §5 p. 23; Definitions 3, 4 and 7; (6)

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Supplement_Pairs

set_option autoImplicit false

namespace DROOptimal.Predictor.Supplement

/-- Theorem 11, p. 26, both clauses, with standing assumptions of §2, p. 5,
and §5, p. 23. The selector is any quasi-continuous selector of the constructed
robust predictor, as in Definition 7 and §5, pp. 24–25.
Every positive constant shift is feasible for r ≥ 0. For r > 0 the unshifted
pair is preferred to every feasible pair; its feasibility is not asserted.
The proof's last sentence on p. 37 has ε > 0 where the statement has r > 0. -/
theorem theorem_11 {n d : ℕ}
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : IsCompact X)
    (Ξ : Set (EuclideanSpace ℝ (Fin d))) (hΞ : IsCompact Ξ)
    (γ : ↥X → ↥Ξ → ℝ) (hγ : Continuous (fun p : ↥X × ↥Ξ => γ p.1 p.2))
    (r : ℝ) (hr : 0 ≤ r)
    (xhat_r : DROOptimal.Continuous.Dist Ξ → ↥X)
    (hquasi : QuasiContinuous xhat_r)
    (hargmin : IsArgminSelector (DROOptimal.Continuous.drPredictor γ r) xhat_r) :
    (∀ ε : ℝ, 0 < ε →
      Feasible6 γ r (fun x P' => DROOptimal.Continuous.drPredictor γ r x P' + ε) xhat_r) ∧
    (0 < r → ∀ (chat : ↥X → DROOptimal.Continuous.Dist Ξ → ℝ)
      (xhat : DROOptimal.Continuous.Dist Ξ → ↥X),
      Feasible6 γ r chat xhat →
        PairLE (DROOptimal.Continuous.drPredictor γ r) xhat_r chat xhat) := by sorry

end DROOptimal.Predictor.Supplement
