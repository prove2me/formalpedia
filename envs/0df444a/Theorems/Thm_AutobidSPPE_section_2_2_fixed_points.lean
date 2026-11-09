-- Prove2me | Theorems.Thm_AutobidSPPE_section_2_2_fixed_points
-- name    : AutobidSPPE.section_2_2_fixed_points
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:03:01.633802+00:00
-- url     : https://prove2.me/theorems/0821e686-2da0-410f-9e50-3f5714818ffb
-- title:
--   §2.2, (6)–(8) — endpoint identities; fixed points of $r$ are exactly the Bayesian SPPEs
-- statement:
--   Throughout, $n\ge2$ bidders have independent values $v_i\sim\mathrm{Unif}[0,\bar v_i]$ with $0<\bar v_i$, and budgets $\rho_i>0$.
--
--   1. For every multiplier profile $\alpha\in[0,1]^n$, with endpoint coordinates $y_i=\bar v_i\alpha_i$ and every bidder $i$,
--   $$
--   s_i(\alpha)=\mathsf s_i(y),\qquad \mathsf b_i(y_{-i})=\bar v_i\,r_i(\alpha_{-i}).
--   $$
--   2. A profile $\alpha$ is a Bayesian SPPE (Problem 1.1) if and only if $\alpha\in[0,1]^n$ and $r_i(\alpha_{-i})=\alpha_i$ for every $i$: the fixed points of the response map are precisely the Bayesian SPPEs.
--
--   This links the equilibrium notion of Problem 1.1 to the dynamics, whose fixed points are those of $r$, and moves the analysis to endpoint coordinates.
--
--   **Formalization Note** The statement holds for every deterministic single-winner tie rule.
--
--   Differences from the source:
--   - generalization: a fixed tie-breaking rule → every deterministic single-winner tie rule (universally quantified); reason: the statement for every rule specializes to the paper's fixed rule
--   - reading: x_i(α) := 1{α_i v_i ≥ max_j α_j v_j} using a fixed tie-breaking rule (Problem 1.1) → x_i = 1 iff bidder i is the one bidder the tie rule picks among the highest bids; reason: under the literal ≥ every tied bidder wins and the all-zero profile is a second SPPE, contradicting the uniqueness the paper proves; §2.2 ('An arbitrary fixed tie rule is used … zero-bid ties pay zero') fixes the single-winner reading
--   - encoding: max in the response (5)/(7) → sSup of the feasible set; reason: the feasible set is a nonempty bounded closed interval (Lemma 2.7), so its supremum is its maximum
--   - encoding: bidders 1, …, n in a fixed order → bidders Fin n in their natural order, paper bidder i = index i − 1; reason: relabeling; every ordering is a relabeling of Fin n, and no instance changes
-- source:
--   Chen–Morgenstern–Yang, Convergent Dynamics in Second Price Autobidding Games, STOC 2027 submission (manuscript sha256 185cb93f…77659a6), §2.2, (5)–(8), p.10

import Mathlib
import Definitions.Def_AutobidSPPE_spend
import Definitions.Def_AutobidSPPE_IsBayesianSPPE
import Definitions.Def_AutobidSPPE_response
import Definitions.Def_AutobidSPPE_endpointSpend
import Definitions.Def_AutobidSPPE_endpointResponse

namespace AutobidSPPE

/-- §2.2, (6)–(8), p.10 (Chen–Morgenstern–Yang, *Convergent Dynamics in Second Price Autobidding Games*, STOC 2027 submission manuscript (sha256 185cb93f…77659a6)): in endpoint coordinates `yᵢ = v̄ᵢαᵢ`, `sᵢ(α) = 𝗌ᵢ(y)` and
`𝖻ᵢ(y₋ᵢ) = v̄ᵢrᵢ(α₋ᵢ)` for every `α ∈ [0,1]ⁿ`; and the fixed points of the response map `r` in
`[0,1]ⁿ` are precisely the Bayesian SPPEs.

**Formalization Note** Every single-winner tie rule is allowed. -/
theorem section_2_2_fixed_points {n : ℕ} (hn : 2 ≤ n) (vbar ρ : Fin n → ℝ) (hvbar : ∀ i, 0 < vbar i) (hρ : ∀ i, 0 < ρ i)
    (tie : TieRule n) :
    (∀ α : Fin n → ℝ, (∀ i, α i ∈ Set.Icc (0 : ℝ) 1) → ∀ i,
      spend vbar tie α i = endpointSpend (fun j => vbar j * α j) i ∧
      endpointResponse vbar ρ (fun j => vbar j * α j) i = vbar i * response vbar ρ tie α i) ∧
    ∀ α : Fin n → ℝ, IsBayesianSPPE vbar ρ tie α ↔
      ((∀ i, α i ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ i, response vbar ρ tie α i = α i) := by sorry

end AutobidSPPE
