-- Prove2me | Theorems.Thm_CongestionTaxes_program_12_convex
-- name    : CongestionTaxes.program_12_convex
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:34:37.724739+00:00
-- url     : https://prove2.me/theorems/06f43318-4648-4e0b-9d75-78d8acbd80de
-- title:
--   Proof of Theorem 3, p.19 — program (12) is convex and has a solution
-- statement:
--   Let $G$ be a congestion game whose resource costs satisfy Assumption 1 with $\rho_{\ell_r}<\infty$ for every $r$, and whose agents have nonempty strategy sets. Then:
--
--   1. the feasible set of program (12) is convex, compact and nonempty;
--   2. the objective $\sum_r p_r(v_r)$ is convex and continuous on it;
--   3. program (12) has a solution.
--
--   Theorem 3 takes the parameters of its taxes from "a solution of the convex program (12)"; this result shows the program is convex and the phrase is not vacuous.
--
--   Differences from the source:
--
--   - generalization: (12) is convex → also compactness and nonemptiness of the feasible set, continuity of the objective, and existence of a solution; reason: Theorem 3 presupposes a solution; the printed claim is clauses 1–2 (convexity)
--   - encoding: $y_i\in\Delta(s_i)$, $s_i=|\mathcal A_i|$ → $y_i$ a weight on all subsets of resources, zero outside $\mathcal A_i$; reason: same simplex, embedded in a fixed finite-dimensional space
--   - generalization: Theorem 3's hypothesis $\sup_{\ell\in\mathcal L}\rho_\ell<\infty$ with every $\ell_r\in\mathcal L$ → $\rho_{\ell_r}<\infty$ for every $r$ (no uniform bound); reason: the convexity argument uses only that each $p_r$ is a convergent series; Theorem 3's hypothesis implies it
--   - encoding: agents endowed with feasible allocations → $\mathcal A_i\ne\emptyset$; reason: $\Delta(s_i)$ is empty otherwise
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, proof of Theorem 3, p.19

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_CongestionTaxes_Assumption1
import Definitions.Def_CongestionTaxes_rho
import Definitions.Def_CongestionTaxes_IsFeasible
import Definitions.Def_CongestionTaxes_objective
import Definitions.Def_CongestionTaxes_IsSolution

open scoped ENNReal

namespace CongestionTaxes

/-- Proof of Theorem 3 (Paccagnan, Gairing, arXiv:2105.07480v2, p.19): "(12) is indeed convex".
For a congestion game whose resource costs satisfy Assumption 1 with `ρ_{ℓ_r} < ∞` and whose agents
have nonempty strategy sets, the feasible set of (12) is convex, compact and nonempty, the objective
`∑_r p_r(v_r)` is convex and continuous on it, and (12) has a solution.

**Formalization Note** A point of (12) is a pair `(y, v)` in the finite-dimensional space
`(ι → Finset E → ℝ) × (E → ℝ)`. Existence of a solution is not printed; Theorem 3 speaks of
"a solution of the convex program (12)", and this clause shows that the phrase is not vacuous. -/
theorem program_12_convex {ι E : Type*} [Fintype ι] [Fintype E] [DecidableEq E]
    (G : CongestionPoA.AsymSum.CongestionGame ι E)
    (hℓ : ∀ r, Assumption1 (G.latency r)) (hρ : ∀ r, rho (G.latency r) < ⊤)
    (hne : ∀ i, (G.strategies i).Nonempty) :
    Convex ℝ {p : (ι → Finset E → ℝ) × (E → ℝ) | IsFeasible G p.1 p.2} ∧
    IsCompact {p : (ι → Finset E → ℝ) × (E → ℝ) | IsFeasible G p.1 p.2} ∧
    {p : (ι → Finset E → ℝ) × (E → ℝ) | IsFeasible G p.1 p.2}.Nonempty ∧
    ConvexOn ℝ {p : (ι → Finset E → ℝ) × (E → ℝ) | IsFeasible G p.1 p.2}
      (fun p => objective G p.2) ∧
    ContinuousOn (fun p : (ι → Finset E → ℝ) × (E → ℝ) => objective G p.2)
      {p : (ι → Finset E → ℝ) × (E → ℝ) | IsFeasible G p.1 p.2} ∧
    ∃ y v, IsSolution G y v := by sorry

end CongestionTaxes
