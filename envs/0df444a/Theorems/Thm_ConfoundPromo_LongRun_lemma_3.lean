-- Prove2me | Theorems.Thm_ConfoundPromo_LongRun_lemma_3
-- name    : ConfoundPromo.LongRun.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:34.185859+00:00
-- url     : https://prove2.me/theorems/ad9d3a4e-67ab-49d8-9693-88105fc273d6
-- title:
--   Lemma 3, p. OA–15 — beliefs converge to the truth exponentially fast in the number of high-surplus periods
-- statement:
--   Fix a market satisfying the standing assumptions, $\epsilon>0$ and a prior $\mu_0\in[0,1]$. For a single-price promotion policy $\alpha$ based on the seller's belief ($\alpha\in\mathcal A^P\cap\mathcal A^M$, the class to which §B.5.1 restricts the whole proof of Theorem 1) and a myopic pricing policy, let $t_n$ be the first period at which the number of periods $t'\le t$ with $\mu_{t'}\in M^{\alpha_{t'}}(\epsilon)$ reaches $n$, as in (30), with $t_n=T+1$ if it never does and $\mu_{T+1}=0$ if $\phi=\phi_L$, $\mu_{T+1}=1$ if $\phi=\phi_H$. Then there are constants $\chi,\beta>0$ such that for every horizon $T$, signaling mechanism, single-price belief-based promotion policy and myopic pricing policy, and all $n\ge1$,
--   $$
--   \mathbb E(\mu_{t_n}\mid\phi=\phi_L)\le\chi e^{-\beta n},\qquad \mathbb E(1-\mu_{t_n}\mid\phi=\phi_H)\le\chi e^{-\beta n}.
--   $$
--
--   The lemma converts the separation of Lemma 2 into exponential learning, which bounds the total surplus that periods above $co(W^C)+\epsilon$ can generate.
--
--   **Formalization Note.** The constants are chosen after $\epsilon$ and $\mu_0$ and before $T$, the signal and the policies. The proof of Theorem 1 needs this uniformity to bound the supremum over policies; the page leaves it implicit.
-- source:
--   Gur, Macnamara, Morgenstern & Saban, Information Disclosure and Promotion Policy Design for Platforms, arXiv:1911.09256v5, p. OA–15 (PDF 49), Lemma 3 and (30)

import Mathlib
import Definitions.Def_ConfoundPromo_LongRun_Model

namespace ConfoundPromo.LongRun

open Finset

/-- Lemma 3 (p. OA–15): with t_m as in (30), E(μ_{t_m} | φ = φ_L) ≤ χ e^{−βm} and
E(1 − μ_{t_m} | φ = φ_H) ≤ χ e^{−βm}, with χ, β chosen before the horizon, the signal and the
policies. The promotion policy is single-price and belief-based (α ∈ A^P ∩ A^M, the standing
restriction of §B.5.1, p. OA–14) and the pricing policy is myopic. -/
theorem lemma_3 (M : Market) (hM : M.Standing) (ε : ℝ) (hε : 0 < ε)
    (μ0 : ℝ) (hμ0 : μ0 ∈ Set.Icc (0 : ℝ) 1) :
    ∃ χ β : ℝ, 0 < χ ∧ 0 < β ∧
      ∀ (T n : ℕ) (sig : Signal n) (α : Promo n T) (π : Pricing n T),
        sig.IsValid → α.IsValid → IsSinglePrice M α → IsBeliefBased M μ0 sig α →
        IsMyopic M μ0 sig α π →
        ∀ m : ℕ, 1 ≤ m →
          condExpect M sig α π false (fun s y => hitBelief M ε μ0 sig α π false s y m)
              ≤ χ * Real.exp (-β * m) ∧
          condExpect M sig α π true (fun s y => 1 - hitBelief M ε μ0 sig α π true s y m)
              ≤ χ * Real.exp (-β * m) := by sorry

end ConfoundPromo.LongRun
