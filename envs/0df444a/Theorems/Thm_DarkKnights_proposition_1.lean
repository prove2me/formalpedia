-- Prove2me | Theorems.Thm_DarkKnights_proposition_1
-- name    : DarkKnights.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:43:42.481114+00:00
-- url     : https://prove2.me/theorems/81c6dbf1-af22-4af5-afc4-7e82ef76f85f
-- title:
--   Proposition 1 — an intervening CDS seller raises equilibrium firm value; full hedge, no liquidation, positive premium (corrected: strict only for $\tau>0$)
-- statement:
--   Let $\alpha\in(0,1)$ be the return to scale, $Z>0$ the support of the uniform profit shock, and $\tau\in[0,1)$ the tax rate. Compare the active-CDS-buyer model of §1 with the model of §2, in which a single protection seller can inject equity into the distressed firm.
--
--   1. Both models have a subgame-perfect equilibrium.
--   2. **(a)** For every equilibrium $E_1$ of the first model and every equilibrium $E_2$ of the second,
--   $$
--   V(E_1)\le V(E_2),\qquad\text{with } V(E_1)<V(E_2)\iff \tau>0 .
--   $$
--   3. **(b), (c)** The second model has an equilibrium in which the lender is fully hedged, $h^*=1$, the probability of liquidation is $0$, and the CDS premium is positive.
--   4. **(b), (c)** If $\tau>0$, every equilibrium of the second model has $h^*\ge1$, probability of liquidation $0$, and a positive CDS premium.
--
--   The CDS seller's ability to recapitalize the firm removes liquidation, which lets the firm borrow and invest at the first-best level; the lender's full hedge is what gives the seller the incentive to intervene, and the premium pays for that intervention although no credit event occurs.
--
--   Differences from the source:
--   - correction: (a) ex ante firm value increases → $V(E_1)\le V(E_2)$ always, strictly iff $\tau>0$; reason: at $\tau=0$ both equilibrium values are first best; e.g. $\alpha=1/2$, $Z=2$, $\tau=0$: model 1 has $b^*=0$ by (8), value $\max_k(\sqrt k-k)=1/4$, and model 2 has value $\max_k(\sqrt k-k)=1/4$ by (15)–(17)
--   - correction: (b), (c) hold in equilibrium → for every equilibrium only when $\tau>0$; reason: at $\tau=0$, $(k_{FB},b=0,h=0)$ is also an equilibrium of model 2 (with $b=0$ every $h$ is a best response and the value is first best), with $h=0$ and premium $0$
--   - reading: (b), (c) for the paper's equilibrium at every $\tau$ → there exists an equilibrium with $h^*=1$, liquidation probability $0$ and positive premium; reason: the paper's equilibrium (16)–(17) with $h^*=1$ (p.20) exists for every $\tau\in[0,1)$
--   - reading: a large amount of CDS contracts → $h^*\ge1$ (and $h^*=1$ in clause 3); reason: p.21: 'he is fully hedged, as his hedge ratio is h∗ = 1'; hedge ratios above 1 tie with 1 (Appendix A), so only $h^*\ge1$ holds for every equilibrium
--   - reading: the probability of liquidation is zero; a credit event is never triggered → Lebesgue probability of the liquidation states is $0$; reason: the credit event is liquidation (p.11)
--   - reading: the CDS spread makes the protection seller break even including the equity injection (p.18) → premium $=-\mathbb E[\text{dealer's ex-post payoff}]$; reason: zero NPV for the protection seller (p.8); equals Lemma 4's bracket on the equilibrium path
--   - encoding: Proposition 1 presupposes the equilibria → existence of equilibria of both models stated as clause 1; reason: without it the clauses over all equilibria would be vacuous; the paper constructs the equilibria in (8)–(9) and (16)–(17)
--   - encoding: expectation under $z\sim U[0,Z]$ and the paper's tie conventions → $(1/Z)\int_{[0,Z]}$; ties repay ≻ renegotiate ≻ liquidate, owner accepts when indifferent; reason: the paper's own conventions (pp.15–16); same instances
-- source:
--   Danis, Gamba, Dark Knights: The Rise in Firm Intervention by CDS Investors, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023) of Management Science, doi:10.1287/mnsc.2023.4717, §2, Proposition 1, p.22 (PDF 24); context p.21 (PDF 23)

import Mathlib
import Definitions.Def_DarkKnights_Primitives
import Definitions.Def_DarkKnights_ActiveBuyerModel
import Definitions.Def_DarkKnights_ActiveSellerModel
import Definitions.Def_DarkKnights_ActiveSellerEquilibrium

namespace DarkKnights

/-- **Proposition 1** (an intervening CDS seller raises firm value; full hedging without
liquidation; a positive premium without a credit event).
Danis, Gamba, *Dark Knights*, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023),
doi:10.1287/mnsc.2023.4717, §2, Proposition 1, p.22 (PDF p.24); context p.21 (PDF p.23).

For `α ∈ ]0, 1[`, `Z > 0` and `τ ∈ [0, 1[`:
1. both models have a subgame-perfect equilibrium;
2. (a) for every equilibrium `E₁` of the active-CDS-buyer model and every equilibrium `E₂` of the
   model with an intervening protection seller, `value E₁ ≤ value E₂`, and the inequality is
   strict iff `τ > 0`;
3. (b), (c) model 2 has an equilibrium with hedge ratio `h* = 1`, zero probability of
   liquidation and a positive CDS premium;
4. (b), (c) if `τ > 0`, every equilibrium of model 2 has `h* ≥ 1`, zero probability of
   liquidation and a positive CDS premium.

**Formalization Note** (a) is corrected: at `τ = 0` both equilibrium values equal the first-best
value (e.g. `α = 1/2`, `Z = 2`: both are `1/4`). (b), (c) hold for every equilibrium only when
`τ > 0`: at `τ = 0`, `(k_FB, b = 0, h = 0)` is also an equilibrium of model 2, with premium `0`.
"A large amount of CDS contracts" is the full hedge `h ≥ 1` (p.21, "he is fully hedged, as his
hedge ratio is h∗ = 1"; hedge ratios above `1` tie with `1`, Appendix A). The credit event is
liquidation (p.11). -/
theorem proposition_1 (α Z τ : ℝ) (hα : 0 < α) (hα1 : α < 1) (hZ : 0 < Z) (hτ0 : 0 ≤ τ)
    (hτ1 : τ < 1) :
    Nonempty (Equilibrium1 α Z τ) ∧ Nonempty (Equilibrium2 α Z τ) ∧
      (∀ (E₁ : Equilibrium1 α Z τ) (E₂ : Equilibrium2 α Z τ),
        E₁.value ≤ E₂.value ∧ (E₁.value < E₂.value ↔ 0 < τ)) ∧
      (∃ E₂ : Equilibrium2 α Z τ, E₂.h = 1 ∧ E₂.liqProb = 0 ∧ 0 < E₂.premium) ∧
      (0 < τ → ∀ E₂ : Equilibrium2 α Z τ, 1 ≤ E₂.h ∧ E₂.liqProb = 0 ∧ 0 < E₂.premium) := by sorry

end DarkKnights
