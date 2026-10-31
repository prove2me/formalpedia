-- Prove2me | Theorems.Thm_DarkKnights_lemma_2
-- name    : DarkKnights.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:42:29.523262+00:00
-- url     : https://prove2.me/theorems/41667716-5cfa-44e8-a5a3-221914b3d4e0
-- title:
--   Lemma 2 — the dealer's equity stake $\theta$ for a given new face value $b_n$
-- statement:
--   Let $0\le h\le 1$, $b\ge0$, $0\le b_n\le b$ and $a\ge0$. Define
--   $$
--   \theta=\begin{cases}1-\dfrac{a-hb}{a-b_n} & \text{if } b_n\le hb\le a,\\[4pt] 1 & \text{if } b_n\le hb,\ a<hb,\\[2pt] 0 & \text{if } b_n>hb,\ a\ge hb,\\[2pt] 1 & \text{if } b_n>hb,\ a<hb.\end{cases}
--   $$
--   Then $\theta\in[0,1]$, the owner accepts the offer $(b_n,\theta)$, and no stake $\theta'\in[0,1]$ that the owner accepts gives the dealer a larger ex-post payoff.
--
--   Together with Lemma 3 this pins down the dealer's take-it-or-leave-it offer in every state.
--
--   **Formalization Note** Where $a=b_n=hb$ the fraction is $0/0$; Lean evaluates it to $0$, so $\theta=1$, and there all stakes give the dealer the same payoff.
--
--   Differences from the source:
--   - reading: the protection seller's equity stake is $\theta$ → $\theta$ is accepted and maximizes the dealer's payoff among the stakes the owner accepts; reason: p.16: the dealer proposes the stake that makes the owner indifferent; where several stakes are optimal (the owner gets $0$ either way), Appendix C picks $\theta=1$
--   - encoding: $1-\frac{a-hb}{a-b_n}$ at $a=b_n$ → Lean's $0/0=0$, giving $\theta=1$; reason: the paper's choice $\theta=1$ in this case (Appendix C); every stake is optimal there
--   - reading: Lemma 2 (no bound on $h$ in its sentence) → $0\le h\le1$; reason: §2's standing conjecture $h\le1$ (p.15); for $h>1$ Appendix A gives another $\theta$
-- source:
--   Danis, Gamba, Dark Knights: The Rise in Firm Intervention by CDS Investors, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023) of Management Science, doi:10.1287/mnsc.2023.4717, §2, Lemma 2, pp.16–17 (PDF 18–19); proof Appendix C, pp.42–43 (PDF 44–45)

import Mathlib
import Definitions.Def_DarkKnights_Primitives
import Definitions.Def_DarkKnights_ActiveSellerModel

namespace DarkKnights

/-- **Lemma 2** (the protection seller's equity stake).
Danis, Gamba, *Dark Knights*, Authors' Accepted Manuscript (WRAP 172628, January 20, 2023),
doi:10.1287/mnsc.2023.4717, §2, Lemma 2, pp.16–17 (PDF pp.18–19); proof Appendix C,
pp.42–43 (PDF pp.44–45).

For `0 ≤ h ≤ 1` (the §2 standing conjecture, p.15), `0 ≤ b_n ≤ b` and asset value `a ≥ 0`, let
`θ = 1 − (a − h b)/(a − b_n)` if `b_n ≤ h b ≤ a`; `θ = 1` if `b_n ≤ h b` and `a < h b`;
`θ = 0` if `b_n > h b` and `a ≥ h b`; `θ = 1` if `b_n > h b` and `a < h b`. Then `θ ∈ [0, 1]`,
the owner accepts the offer `(b_n, θ)`, and no stake `θ' ∈ [0, 1]` that the owner accepts gives
the dealer a larger payoff.

**Formalization Note** "The protection seller's equity stake is θ" is read as: `θ` is a
dealer-optimal stake among the stakes the owner accepts, for the given `b_n`. Where
`a = b_n = h b` the printed fraction is `0/0`; Lean's `0/0 = 0` gives `θ = 1`, and there every
stake gives the dealer the same payoff. -/
theorem lemma_2 (a b bn h : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hbn : 0 ≤ bn) (hbnb : bn ≤ b)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    let θ : ℝ :=
      if bn ≤ h * b then (if h * b ≤ a then 1 - (a - h * b) / (a - bn) else 1)
      else (if h * b ≤ a then 0 else 1)
    θ ∈ Set.Icc (0 : ℝ) 1 ∧ accepts a b h (bn, θ) ∧
      ∀ θ' ∈ Set.Icc (0 : ℝ) 1, accepts a b h (bn, θ') →
        dealerPayoff a b h (bn, θ') ≤ dealerPayoff a b h (bn, θ) := by sorry

end DarkKnights
