-- Prove2me | Theorems.Thm_FairExplore_proposition_10
-- name    : FairExplore.proposition_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:15:32.182562+00:00
-- url     : https://prove2.me/theorems/cf18933f-0ac8-49b9-8ea5-8c35eb733b6b
-- title:
--   Proposition 10, p.34 — consistent policies pull a suboptimal arm at least $J^g(a)\log T$ times (corrected: $p_g>0$)
-- statement:
--   Let $\mathcal I$ be a grouped $K$-armed bandit instance with parameter $\theta\in(0,1)^K$ (distinct entries), and let $\pi\in\Psi$ be a consistent policy (admissible and measurable). Let $g$ be a group and $a\in\mathcal A^g_{\mathrm{sub}}$ a suboptimal arm for $g$. Then
--   $$\liminf_{T\to\infty}\frac{\mathbb E[N_T(a)]}{\log T}\ \ge\ J^g(a)=\frac{1}{\mathrm{KL}(\theta(a),\mathrm{OPT}(g))}.$$
--
--   This is the Lai–Robbins lower bound for the grouped model; it gives (8) and the upper bound $SW(\pi,\mathcal I)\le Y^*(\mathcal I)$ of Theorem 2.
--
--   **Formalization Note** The liminf is taken in the extended reals.
--
--   Differences from the source:
--   - correction: p_g ≥ 0 with Σ_g p_g = 1 (p.6) → ∀ g, 0 < p g; reason: with p = (1, 0), A^1 = {2}, A^2 = {1, 2}, θ = (0.3, 0.6), arm 1 is available only to group 2, which never arrives; the consistent policy that always pulls arm 2 has E[N_T(1)] = 0, below J^2(1) log T; the proofs use p_g > 0 throughout (W^g_t, p.34; Claim 3, p.44; p.61)
--   - encoding: any policy → any admissible, measurable policy; reason: a policy of the model pulls an available arm (p.6), and expectations of the run presuppose measurability
--   - reading: consistency / log-consistency over every instance of the class → over every θ ∈ (0,1)^K with distinct entries, the structure (G, p, A^g) fixed; reason: the policy knows every quantity except θ (p.6), so the class it is designed for varies θ
--   - encoding: A = [K], G a finite set → any finite linearly ordered arm type and any finite group type with the discrete σ-algebra; reason: every finite set of arms is order-isomorphic to [K]; the order is only used to index the uniform choice in step 1 of PF-UCB
--   - encoding: times t = 1, 2, …; Pr and E → Lean step s is paper time s + 1; probabilities are measures of events, expectations are ∫⁻ of nonnegative quantities; reason: Lean indexing; same values
-- source:
--   Baek & Farias, Fair Exploration via Axiomatic Bargaining, arXiv:2106.02553v2, Proposition 10, p.34 (proof p.40)

import Mathlib
import Definitions.Def_FairExplore_KArmed

open MeasureTheory Filter

namespace FairExplore

/-- Proposition 10 (Lai–Robbins lower bound for grouped bandits): for a consistent policy
`π ∈ Ψ`, a group `g` and an arm `a ∈ A^g_sub`, `liminf_{T→∞} E[N_T(a)]/log T ≥ J^g(a)`.
Baek & Farias, *Fair Exploration via Axiomatic Bargaining*, arXiv:2106.02553v2, Proposition 10, p.34 (proof p.40).

**Formalization Note** `Ψ` is consistency over the K-armed class with the known structure `S`
(`IsConsistent`). The liminf is taken in `EReal`. -/
theorem proposition_10 {γ α : Type*} [Fintype γ] [MeasurableSpace γ] [DiscreteMeasurableSpace γ] [DecidableEq γ]
    [Fintype α] [DecidableEq α]
    (S : GroupedStructure γ α) (hp : ∀ g, 0 < S.p g)
    (π : Policy γ α) (hπA : IsAdmissible S.A π) (hπM : IsMeasurablePolicy π) (hπ : IsConsistent S π)
    (θ : α → ℝ) (hθ : InKClass θ) (g : γ) (a : α) (ha : a ∈ subG S.A θ g) :
    ((Jg S.A θ g a : ℝ) : EReal)
      ≤ liminf (fun T : ℕ => ((expPulls S θ π T a / Real.log T : ℝ) : EReal)) atTop := by sorry

end FairExplore
