-- Prove2me | Theorems.Thm_CommissionsSubscriptions_theorem_1
-- name    : CommissionsSubscriptions.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:42:38.69799+00:00
-- url     : https://prove2.me/theorems/5f52b1a1-21ce-497e-a1e8-2b03ad21a6cc
-- title:
--   Theorem 1 — the relaxation (7) is tight and optimal fees are characterized by (8) (corrected: in (ii) the flow $\bar x$ in (8) ranges over the optimal solutions of (7))
-- statement:
--   Consider a networked market with finitely many seller types $S$ (at least one) and buyer types $B$, satisfying the standing hypotheses of §2 (positive masses, $c\ge0$, every type of degree at least one, Assumption 1) and Assumption 2. Let $(\bar x,\bar q^s,\bar q^b)$ be an optimal solution of the relaxation (7). Then:
--
--   **(i)** Problem (7) is a tight relaxation of the platform's problem (3):
--
--   1. optimal solutions of (3) exist: some fees $(\gamma,\mu)\in\Gamma\times\mathcal U$ and equilibrium $(p,x,q^s,q^b)\in X(\gamma,\mu)$ attain $V_{opt}$;
--   2. $V_{opt}=\tilde V_{opt}=h(\bar q^s,\bar q^b)$;
--   3. every optimal solution of (3) has supply-demand vector $(\bar q^s,\bar q^b)$.
--
--   **(ii)** 1. The optimal commission-subscription pair is not unique.
--
--   For every $(\gamma,\mu)\in\Gamma\times\mathcal U$ with $\gamma^s_i<1$ for all $i$, with $\tilde\gamma^s_i=\frac1{1-\gamma^s_i}$, $\tilde\mu^s_i=\frac{\mu^s_i}{1-\gamma^s_i}$, $\tilde\gamma^b_j=\frac1{1+\gamma^b_j}$, $\tilde\mu^b_j=\frac{\mu^b_j}{1+\gamma^b_j}$:
--
--   2. if some price vector $p$ satisfies the system (8) with respect to $(\bar x,\bar q^s,\bar q^b)$,
--   $$\begin{aligned}&p_i-\tilde\mu^s_i-F^{-1}_{s_i}(\bar q^s_i/s_i)\tilde\gamma^s_i=0\ (\bar q^s_i>0),\qquad p_i-\tilde\mu^s_i\le0\ (\bar q^s_i=0),\\ &p_i+\tilde\mu^b_j+c_i\tilde\gamma^b_j-F^{-1}_{b_j}(1-\bar q^b_j/b_j)\tilde\gamma^b_j=0\ (\bar x_{ij}>0),\quad \ge0\ (\bar x_{ij}=0),\\ &\tilde\gamma^s_i\ge1,\ \tilde\mu^s_i\ge0,\ p_i\ge0,\qquad 0\le\tilde\gamma^b_j\le1,\ \tilde\mu^b_j\ge0,\end{aligned}$$
--   then $(\gamma,\mu)$ is an optimal commission-subscription pair;
--   3. $(\gamma,\mu)$ is an optimal commission-subscription pair **if and only if** there are an optimal solution $(x',\bar q^s,\bar q^b)$ of (7) and a price vector $p$ satisfying (8) with respect to $(x',\bar q^s,\bar q^b)$.
--
--   The nonconvex problem of choosing fees whose induced competitive equilibrium maximizes revenue is thus solved by a convex network-flow problem, and the optimal fees are described by a linear system.
--
--   Differences from the source:
--   - correction: (ii) for the fixed optimal solution (x̄, q̄^s, q̄^b) of (7): (γ, µ) is optimal if and only if some p ∈ ℝ^{|S|}_+ satisfies (8) with respect to x̄ → (ii-2) the “if” for the fixed x̄; (ii-3) (γ, µ) is optimal iff for some optimal solution (x′, q̄^s, q̄^b) of (7) some p satisfies (8) with respect to x′; reason: the printed “only if” is false for some optimal x̄: S = B = {1,2}, E complete, s = b = (1,1), c = (0, 1/10), all four distributions uniform on [0,1]; q̄^s = (21/80, 17/80), q̄^b = (19/80, 19/80); γ = 0 except γ^b_2 = 1, µ^s = 0, µ^b = (1/2, 19/80) is optimal (equilibrium p = (21/80, 17/80) with flow (x₁₁,x₁₂,x₂₁,x₂₂) = (19/80, 1/40, 0, 17/80), revenue 363/1600 = Ṽ_opt), but for the optimal flow x̄ = (21/160, 21/160, 17/160, 17/160), (8a) forces p = (21/80, 17/80) and (8c) at (2,1) gives 17/80 + 1/2 + 1/10 − 61/80 = 1/20 ≠ 0; the gap is step (ii-2)'s “let p be such that (p, x̄, q̄^s, q̄^b) ∈ X(γ, µ)”
--   - encoding: seller and buyer types S = {1,…,n}, B = {1,…,m} → arbitrary finite types S, B with decidable equality; reason: a finite index set is a relabeling of {1,…,n}; the same instances
--   - encoding: inverse distributions F⁻¹ : [0,1] → [0, v̄] with v̄ ∈ ℝ₊ ∪ {∞}, and footnote 4's F⁻¹(1)·0 = 0 → Finv F u = inf{r ≥ 0 : u ≤ F r} in EReal with inf ∅ = ⊤ (Reading 1); reason: under Assumption 1 this is the paper's F⁻¹ on [0,1], with Finv F 1 = v̄ = ⊤ for unbounded support; EReal's ⊤·0 = 0 is footnote 4
--   - encoding: Assumption 1: nonatomic F on [0, v̄], extended to ℝ by 0 and 1, C¹ and strictly increasing on (0, v̄), bounded mean ∫₀^{v̄}(1 − F) < ∞ → IsValueCDF: monotone, 0 on (−∞,0], continuous, F → 1 at +∞, strictly increasing and C¹ on (0, Finv F 1), 1 − F integrable on (0,∞) (Reading 2); reason: the same class of extended CDFs; 1 − F vanishes beyond v̄, so the two integrals agree
--   - reading: Assumption 2: u F⁻¹_{b_j}(1 − u) and −u F⁻¹_{s_i}(u) strictly concave in u ∈ [0,1] → buyer function strictly concave on [0,1] (value 0 at u = 0, footnote 4); seller function strictly concave on [0,1) (Reading 3); reason: the seller function equals −v̄ = −∞ at u = 1 for unbounded support, where only the half-open reading is meaningful; for bounded support it is continuous at 1 and strict concavity on [0,1) and on [0,1] are equivalent
--   - encoding: flow vector x ∈ ℝ^{|E|} → x : S → B → ℝ, read only on E (Reading 6); reason: entries off E occur in no constraint or objective
--   - encoding: h(q^s, q^b) of (6) / objective (7a), with h_i(s_i) = ∞ for unbounded seller support → obj7 in EReal: real buyer sum minus the EReal seller sum minus the real cost sum; reason: a seller term +∞ gives −∞ as in the paper; the buyer terms are finite on [0, b_j], so no ⊤ − ⊤ arises
--   - encoding: min_{i′:(i′,j)∈E} {(1 + γ^b_j) p_{i′} + c_{i′}} in (2b) and argmin in (2d) → minCost: ℝ-infimum over the neighbour subtype; i ∉ argmin written as (1 + γ^b_j)p_i + c_i ≠ minCost (Reading 7); reason: the neighbour set is finite and nonempty (every type has degree ≥ 1, in MarketHyp), so the infimum is the minimum
--   - encoding: V_opt = max over the feasible set of (3) → Vopt: supremum in EReal of (3a) over the feasible set of (3) (Reading 5); reason: attainment of the maximum is stated separately (Theorem 1(i)); the supremum equals the max when it is attained
--   - encoding: (γ, µ) optimal: V(γ, µ) = V_opt, V(γ, µ) the revenue under (γ, µ) → IsOptimalPair: (γ, µ) ∈ Γ × U and some equilibrium under (γ, µ) has revenue V_opt (Reading 4); reason: V(γ, µ) is well defined because equilibria exist (Proposition 1) and all have the same revenue (Corollary 1), both milestones
--   - encoding: (8a)/(8c) “expression − F⁻¹·γ̃ = 0” and (8d) “expression − F⁻¹·γ̃ ≥ 0”, (i,j) ranging over pairs → “expression = F⁻¹·γ̃” and “F⁻¹·γ̃ ≤ expression” in EReal, (i,j) ranging over E; reason: identical on finite values; when the F⁻¹ term is +∞ both forms are false; x̄ is only defined on E
--   - encoding: S = {1,…,n} with n ≥ 1 → [Nonempty S]; reason: the paper's index sets are nonempty; with S = ∅ (hence B = ∅) there is only one fee vector and the non-uniqueness clause is false for a degenerate reason
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), Theorem 1, p. 13 (proof EC.3.1, pp. ec38–ec44)

import Mathlib
import Definitions.Def_CommissionsSubscriptions_MarketHyp
import Definitions.Def_CommissionsSubscriptions_Assumption2
import Definitions.Def_CommissionsSubscriptions_IsOptimalPair
import Definitions.Def_CommissionsSubscriptions_IsOptimal7
import Definitions.Def_CommissionsSubscriptions_System8

namespace CommissionsSubscriptions

/-- **Theorem 1 — the relaxation (7) is tight, and optimal commission-subscription pairs are
characterized by the system (8)** (corrected: in (ii) the flow `x̄` in (8) ranges over the
optimal solutions of (7)).
Birge, Candogan, Chen, Saban, *Optimal Commissions and Subscriptions in Networked Markets*,
SSRN 3259716 (version of 2019-09-13), Theorem 1, p. 13 (proof EC.3.1, pp. ec38–ec44).

Under the standing hypotheses of §2 (finitely many seller and buyer types, `S` nonempty, positive
masses, `c ≥ 0`, every type of degree at least one, Assumption 1) and Assumption 2, let
`(x̄, q̄^s, q̄^b)` be an optimal solution of (7). Then:

(i) (7) is a tight relaxation of (3):
  1. optimal solutions of (3) exist, i.e. some feasible tuple of (3) attains `V_opt`;
  2. `V_opt = Ṽ_opt = h(q̄^s, q̄^b)`;
  3. every optimal solution of (3) has supply-demand vector `(q̄^s, q̄^b)`.

(ii) 1. The optimal commission-subscription pair is not unique.
  For every `(γ, µ) ∈ Γ × U` with `γ^s_i < 1` for all `i`:
  2. if some price vector `p` satisfies (8) with respect to `(x̄, q̄^s, q̄^b)`, then `(γ, µ)` is
     optimal (the printed "if", for the given `x̄`);
  3. `(γ, µ)` is optimal if and only if, for some optimal solution `(x′, q̄^s, q̄^b)` of (7),
     some price vector `p` satisfies (8) with respect to `(x′, q̄^s, q̄^b)`.

**Formalization Note.** Correction: the printed (ii) says "`(γ, µ)` is optimal iff there is `p`
satisfying (8)" with `x̄` the theorem's fixed optimal flow. Its "only if" fails for some choices
of `x̄`, because (7) can have several optimal flows and (8c)/(8d) depend on the support of `x̄`:
with `S = B = {1,2}`, `E` complete, `s = b = (1,1)`, `c = (0, 1/10)`, all four distributions
uniform on `[0,1]`, `γ = 0` except `γ^b_2 = 1`, `µ^s = 0`, `µ^b = (1/2, 19/80)`, the pair is
optimal (it implements `q̄^s = (21/80, 17/80)`, `q̄^b = (19/80, 19/80)` with the flow
`(x₁₁, x₁₂, x₂₁, x₂₂) = (19/80, 1/40, 0, 17/80)` at `p = (21/80, 17/80)`, revenue
`363/1600 = Ṽ_opt`), but for the optimal flow `x̄ = (21/160, 21/160, 17/160, 17/160)` (8a) forces
`p = (21/80, 17/80)` and (8c) at `(2,1)` fails. Clause (ii)3 quantifies the flow existentially;
clause (ii)2 keeps the printed "if" for the given `x̄`.
Conventions: `V_opt` is an `EReal` supremum (Reading 5); optimal pairs are `IsOptimalPair`
(Reading 4); `F⁻¹` is `EReal`-valued (Reading 1); see the definitions for Readings 2, 3, 6–8. -/
theorem theorem_1 {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    [Nonempty S] (M : Market S B) (hM : MarketHyp M) (hA2 : Assumption2 M)
    (xbar : S → B → ℝ) (qsbar : S → ℝ) (qbbar : B → ℝ) (hopt : IsOptimal7 M xbar qsbar qbbar) :
    -- (i)
    ((∃ (f : Fees S B) (p : S → ℝ) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ),
        Feasible3 M f p x qs qb ∧ ((revenue M f p x : ℝ) : EReal) = Vopt M) ∧
      Vopt M = obj7 M qsbar qbbar ∧
      (∀ (f : Fees S B) (p : S → ℝ) (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ),
        Feasible3 M f p x qs qb → ((revenue M f p x : ℝ) : EReal) = Vopt M →
          qs = qsbar ∧ qb = qbbar)) ∧
    -- (ii)
    ((∃ f f' : Fees S B, f ≠ f' ∧ IsOptimalPair M f ∧ IsOptimalPair M f') ∧
      (∀ f : Fees S B, InGammaU f → (∀ i, f.gs i < 1) →
        ((∀ p : S → ℝ, System8 M xbar qsbar qbbar f p → IsOptimalPair M f) ∧
          (IsOptimalPair M f ↔
            ∃ x' : S → B → ℝ, IsOptimal7 M x' qsbar qbbar ∧
              ∃ p : S → ℝ, System8 M x' qsbar qbbar f p)))) := by sorry

end CommissionsSubscriptions
