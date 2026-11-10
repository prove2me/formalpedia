-- Prove2me | Theorems.Thm_BilatMatch_lemma_2_1
-- name    : BilatMatch.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:11:31.099676+00:00
-- url     : https://prove2.me/theorems/1c67984f-c69a-4b2b-b4a2-305d5e98f3b1
-- title:
--   Lemma 2.1 (Payments and Budget Duality) — $\Lambda(x)$ is the maximal revenue; $\mathrm{SB}=\min_{\alpha\ge0}V_\alpha$, $V_\alpha=\max_{x\in X}L_\alpha(x)$
-- statement:
--   Consider a market with finitely many agents, independent finitely supported priors, and a nonempty downward-closed family of feasible matchings; reports range over the supports. Then:
--
--   1. for every $x\in X$, the largest expected net revenue of an admissible BIC, IIR mechanism implementing $x$ equals
--   $$\Lambda(x)=\mathbb E\Big[\sum_i\phi_i(v_i)x_{B_i}\Big]-\mathbb E\Big[\sum_j\tau_j(c_j)x_{S_j}\Big],$$
--   and it is attained;
--   2. an allocation is implementable with BIC, IIR and ex-ante weak budget balance exactly when $x\in X$ and $\Lambda(x)\ge0$;
--   3. $\mathrm{SB}=\min_{\alpha\ge0}V_\alpha$, with the minimum attained;
--   4. for every $\alpha\ge0$, $V_\alpha=\max_{x\in X}\{\mathrm{GFT}(x)+\alpha\Lambda(x)\}$, with the maximum attained.
--
--   This is the budget duality that turns the second-best problem into the family of fixed-multiplier Lagrangian problems used throughout the paper.
--
--   **Formalization Note** A mechanism implements $x$ when its edge trade probabilities equal $x$ at every support profile. "min" and "max" are stated as attained extrema.
--
--   Differences from the source:
--   - encoding: an allocation is implementable by a mechanism → an admissible mechanism whose edge trade probabilities equal x at every support profile; reason: only support profiles carry probability; admissibility (footnote 1) is the paper's standing well-definedness
--   - encoding: SB = min_{α≥0} V_α and V_α = max_{x∈X} → IsLeast of the set of V_α (α ≥ 0) at SB, and an x ∈ X attaining the maximum with V_α equal to its value; reason: min and max are attainment claims; both are kept
-- source:
--   Liu, Qin, Wang, From Bilateral Trade to Matching Markets: Sharp Gains from Trade, arXiv:2609.30702 (held version, sha256 ff1490ad…), Lemma 2.1, p.7 (pdf p.9)

import Mathlib
import Definitions.Def_BilatMatch_InX
import Definitions.Def_BilatMatch_ValphaOn

open MeasureTheory

namespace BilatMatch

/-- **Lemma 2.1 (Payments and Budget Duality).** Liu, Qin, Wang, arXiv:2609.30702 (held version,
sha256 ff1490ad…), Lemma 2.1, p.7 (pdf p.9).

For finitely many agents with independent finitely supported priors:
1. for every `x ∈ X`, the largest expected net revenue of a BIC, IIR mechanism implementing `x` is
   `Λ(x) = E[∑_i ϕ_i(v_i) x_{B_i}] − E[∑_j τ_j(c_j) x_{S_j}]` (attained);
2. `x` is implementable with BIC, IIR and ex-ante WBB iff `x ∈ X` and `Λ(x) ≥ 0`;
3. `SB = min_{α ≥ 0} V_α` (the minimum is attained);
4. `V_α = max_{x ∈ X} (GFT(x) + α Λ(x))` for every `α ≥ 0` (the maximum is attained).

**Formalization Note** Reports range over the supports of the priors (`suppDomain`, p.6); a mechanism
implements `x` when its edge trade probabilities equal `x` at every support profile. `V_α` and `SB`
are the mechanism suprema with these report domains. -/
theorem lemma_2_1 {B S : Type*} [Fintype B] [Fintype S] (I : Market B S) (hI : I.IsValid)
    (hB : ∀ i, IsFiniteSupport (I.buyerLaw i)) (hS : ∀ j, IsFiniteSupport (I.sellerLaw j)) :
    (∀ x : Allocation B S, InX I x →
      IsGreatest {r : ℝ | ∃ A : Mechanism I, A.Admissible ∧ A.IsBICOn (suppDomain I) ∧
        A.IsIIROn (suppDomain I) ∧ A.Realizes x ∧ r = A.Rev} (Lambda I x)) ∧
    (∀ x : Allocation B S, (∃ A : Mechanism I, A.Admissible ∧ A.IsBICOn (suppDomain I) ∧
        A.IsIIROn (suppDomain I) ∧ A.Realizes x ∧ 0 ≤ A.Rev) ↔ (InX I x ∧ 0 ≤ Lambda I x)) ∧
    IsLeast {V : EReal | ∃ α : ℝ, 0 ≤ α ∧ V = ValphaOn I (suppDomain I) α}
      (SBOn I (suppDomain I)) ∧
    (∀ α : ℝ, 0 ≤ α → ∃ x : Allocation B S, InX I x ∧
      (∀ y : Allocation B S, InX I y → lagrangian I α y ≤ lagrangian I α x) ∧
      ValphaOn I (suppDomain I) α = ((lagrangian I α x : ℝ) : EReal)) := by sorry

end BilatMatch
