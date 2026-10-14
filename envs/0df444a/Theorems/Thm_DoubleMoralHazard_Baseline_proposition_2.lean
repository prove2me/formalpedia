-- Prove2me | Theorems.Thm_DoubleMoralHazard_Baseline_proposition_2
-- name    : DoubleMoralHazard.Baseline.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:54:16.079488+00:00
-- url     : https://prove2.me/theorems/b75ed123-1c1e-4016-b2b8-8f41c2a29b30
-- title:
--   Proposition 2, p. 20 — for γ ∈ Γ^IC with u(γ, ν̄, Nᵘ) = w, Fᵢ(w) ≥ U(γ, ν̄, Nᵘ)
-- statement:
--   Fix a scenario $i\in\{1,2,3\}$ ($c\le\mu pR^u$; $\mu pR^u<c<\mu R^u$; $c\ge\mu R^u$) and let $F_i$ be a solution of the scenario's value-function equation, extended beyond the tenure threshold by
--   $$F_i(w)=F_i(\bar w^i)-(w-\bar w^i)\qquad(w>\bar w^i).$$
--   Then for every contract $\gamma\in\Gamma^{IC}$ and every $w\ge0$ with $u(\gamma,\bar\nu,N^u)=w$,
--   $$F_i\big(u(\gamma,\bar\nu,N^u)\big)\ \ge\ U(\gamma,\bar\nu,N^u).$$
--
--   The value function $F_i$ is therefore an upper bound on the principal's utility under any incentive compatible contract that promises the agent $w$; with Proposition 1 it shows that the contracts $\gamma^i$ trace out the optimal frontier.
--
--   **Formalization Note** The page states the bound for $w\in[0,\bar w^i]$; it is stated here for every $w\ge0$, which is what the proof (Lemma 14 applied to the extended $F_i$) delivers and what the optimality argument (2.15) uses for contracts promising more than $\bar w^i$. The extension beyond $\bar w^i$ is part of the solution notion of $F_i$. Scenario 2 uses the corrected (2.11).
-- source:
--   Tian, Astashkina and Duenyas, Dynamic Contract Design in the Presence of Double Moral Hazard, SSRN 4249177 (preprint, PDF sha256 dfddb801…), p. 20, Proposition 2; proof Appendix B.6, pp. 49–51 (Lemma 14, (B.12)–(B.16))

import Mathlib
import Definitions.Def_DoubleMoralHazard_Baseline_Params
import Definitions.Def_DoubleMoralHazard_Baseline_HJB
import Definitions.Def_DoubleMoralHazard_Baseline_Arrivals
import Definitions.Def_DoubleMoralHazard_Baseline_Contracts
import Definitions.Def_DoubleMoralHazard_Baseline_TenureContracts

namespace DoubleMoralHazard.Baseline

/-- Proposition 2, p. 20: in scenario `i`, every contract `γ ∈ Γ^IC` that gives the agent the
utility `u(γ, ν̄, Nᵘ) = w` gives the principal at most `Fᵢ(w)`, where `Fᵢ` is extended beyond the
tenure threshold by `Fᵢ(w) = Fᵢ(w̄ⁱ) - (w - w̄ⁱ)`. Stated for every `w ≥ 0`. -/
theorem proposition_2 (P : Params) :
    (P.c ≤ P.mu * P.p * P.Ru → ∀ F : ℝ → ℝ, IsSol1 P F → ∀ γ ∈ GammaIC P, ∀ w : ℝ, 0 ≤ w →
      u P γ sbar = ENNReal.ofReal w → U P γ ≤ F w) ∧
    (P.mu * P.p * P.Ru < P.c ∧ P.c < P.mu * P.Ru → ∀ F : ℝ → ℝ, IsSol2 P F →
      ∀ γ ∈ GammaIC P, ∀ w : ℝ, 0 ≤ w →
      u P γ sbar = ENNReal.ofReal w → U P γ ≤ F w) ∧
    (P.mu * P.Ru ≤ P.c → ∀ F : ℝ → ℝ, IsSol3 P F → ∀ γ ∈ GammaIC P, ∀ w : ℝ, 0 ≤ w →
      u P γ sbar = ENNReal.ofReal w → U P γ ≤ F w) := by sorry

end DoubleMoralHazard.Baseline
