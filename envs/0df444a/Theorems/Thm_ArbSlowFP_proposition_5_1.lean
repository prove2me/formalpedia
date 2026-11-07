-- Prove2me | Theorems.Thm_ArbSlowFP_proposition_5_1
-- name    : ArbSlowFP.proposition_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:51:43.193196+00:00
-- url     : https://prove2.me/theorems/f6302d29-cdcd-4798-94f4-1d314bd4771d
-- title:
--   Proposition 5.1 — the RPS clock is an order-2 clock with unique best responses
-- statement:
--   The data $(10)$–$(11)$ with entry action $b=0$ and counter $v=(0,-1,1)$ define an order-2 clock on $3$ actions, with $Q_2=1$, $\delta_0=1$, $A_2=1$ and $\hat Q_2(\epsilon)=1$ for all $\epsilon>0$. With the setup action there are four actions in total. Every best response in the phase words is unique: at every proper prefix of $W_2(q)$, $q\ge1$, the next action is the strict maximizer of the score.
--
--   This is the base case of the induction.
--
--   **Formalization Note** The values are the fields of `rpsClockData`. The four actions are the type `Option (Fin 3)`.
--
--   Differences from the source:
--   - encoding: the priority of the clock is left unnamed → 0 ≺ 1 ≺ 2 in rpsClockData; reason: best responses in the words are unique, so the priority never decides a play
--   - encoding: a total priority order ≺ → an injective rank function, lower rank first; reason: same orders; a finite total order is an injective rank
--   - encoding: integer count table C ∈ ℤ^{m×k} → rational matrix with a clause that every entry is an integer; reason: one numeric type for the tables; same instances
--   - encoding: Q̂_k(ϵ) for rational ϵ > 0 → Qhat a b at ϵ = (a+1)/(b+1), with Computable₂ Qhat, inside IsClock; reason: (a+1)/(b+1) reaches every positive rational; Mathlib has no Primcodable ℚ
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), p.32, Proposition 5.1

import Mathlib
import Definitions.Def_ArbSlowFP_rpsClockData

open Matrix

namespace ArbSlowFP

/-- Proposition 5.1, p.32 (arXiv:2610.08768, version of November 3, 2026, sha256 977c34b6…): (10)–(11)
with `b = 0`, `v = (0, -1, 1)`, `Q₂ = 1`, `δ₀ = 1`, `A₂ = 1`, `Q̂₂(ϵ) = 1` define an order-2 clock on 3
actions (these values are the fields of `rpsClockData`); adjoining the setup action gives four actions;
every best response in its phase words is unique.

**Formalization Note.** The action type with a setup action is `Option (Fin 3)`, as in `setupGame`. -/
theorem proposition_5_1 :
    IsClock rpsClockData ∧
    Fintype.card (Option (Fin 3)) = 4 ∧
    ∀ q, 1 ≤ q → ∀ h (hh : h < (rpsW q).length),
      IsUniqueMax (scoreAfter rpsA (rpsClockData.r q) ((rpsW q).take h)) ((rpsW q)[h]) := by sorry

end ArbSlowFP
