-- Prove2me | Theorems.Thm_AutobidSPPE_lemma_2_20
-- name    : AutobidSPPE.lemma_2_20
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:11:04.407466+00:00
-- url     : https://prove2.me/theorems/3f15e857-d498-46f5-9628-efd95a92b6da
-- title:
--   Lemma 2.20 — multiplier distance controlled by the potential
-- statement:
--   Throughout, $n\ge2$ bidders have independent values $v_i\sim\mathrm{Unif}[0,\bar v_i]$ with $0<\bar v_i\le\hat v_i<\infty$ (true supports $\bar v$, certified upper bounds $\hat v$), and budgets $\rho_i>0$; the constants of (10)–(12) are computed from $\hat v$ and $\rho$. Let $\alpha^*$ be the Bayesian SPPE. For every multiplier profile $\alpha$ with $y=\bar v\alpha\in\mathcal Y$,
--   $$
--   \|\alpha-\alpha^*\|_\infty\le P_{\mathrm{err}}\sqrt{\mathcal V(\alpha)}. \tag{48}
--   $$
--   No lower bound on the unknown support endpoints is needed.
--
--   Differences from the source:
--   - encoding: ‖·‖_∞ → the sup norm of Fin n → ℝ (and of functions on index subtypes); reason: Lean's norm on finite products is the maximum norm
--   - generalization: a fixed tie-breaking rule → every deterministic single-winner tie rule (universally quantified); reason: the statement for every rule specializes to the paper's fixed rule
--   - reading: x_i(α) := 1{α_i v_i ≥ max_j α_j v_j} using a fixed tie-breaking rule (Problem 1.1) → x_i = 1 iff bidder i is the one bidder the tie rule picks among the highest bids; reason: under the literal ≥ every tied bidder wins and the all-zero profile is a second SPPE, contradicting the uniqueness the paper proves; §2.2 ('An arbitrary fixed tie rule is used … zero-bid ties pay zero') fixes the single-winner reading
--   - encoding: bidders 1, …, n in a fixed order → bidders Fin n in their natural order, paper bidder i = index i − 1; reason: relabeling; every ordering is a relabeling of Fin n, and no instance changes
--   - encoding: max in the response (5)/(7) → sSup of the feasible set; reason: the feasible set is a nonempty bounded closed interval (Lemma 2.7), so its supremum is its maximum
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), Lemma 2.20, (48), p.24

import Mathlib
import Definitions.Def_AutobidSPPE_IsBayesianSPPE
import Definitions.Def_AutobidSPPE_endpointBox
import Definitions.Def_AutobidSPPE_potential
import Definitions.Def_AutobidSPPE_Perr

namespace AutobidSPPE

/-- Lemma 2.20, p.24 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6)): for every `α` with `y = v̄α ∈ 𝒴`,
`‖α − α*‖_∞ ≤ P_err √𝒱(α)` (48), where `α*` is the Bayesian SPPE. -/
theorem lemma_2_20 {n : ℕ} (hn : 2 ≤ n) (vbar vhat ρ : Fin n → ℝ) (hvbar : ∀ i, 0 < vbar i ∧ vbar i ≤ vhat i)
    (hρ : ∀ i, 0 < ρ i)
    (tie : TieRule n) :
    ∀ αstar : Fin n → ℝ, IsBayesianSPPE vbar ρ tie αstar →
      ∀ α : Fin n → ℝ, (fun i => vbar i * α i) ∈ endpointBox vbar ρ →
        ‖α - αstar‖ ≤ Perr vhat ρ * Real.sqrt (potential vbar vhat ρ α) := by sorry

end AutobidSPPE
