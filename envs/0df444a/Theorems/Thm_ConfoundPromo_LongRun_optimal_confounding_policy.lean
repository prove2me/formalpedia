-- Prove2me | Theorems.Thm_ConfoundPromo_LongRun_optimal_confounding_policy
-- name    : ConfoundPromo.LongRun.optimal_confounding_policy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:51.046987+00:00
-- url     : https://prove2.me/theorems/feac1409-c64d-4bb6-a868-362bdd3bde47
-- title:
--   Proof of Theorem 1, p. OA–17, Existence of Optimal Confounding Promotion Policy — repeating a one-period confounding rule T times yields T times its surplus
-- statement:
--   Fix a market satisfying the standing assumptions, a horizon $T\ge1$ and a belief $\mu_1\in[0,1]$. Let $a(p,\phi)\in[0,1]$ be a single-price one-period promotion rule and $p$ a myopic price against it at belief $\mu_1$ (Definition 1) such that the seller's posterior after either sale outcome is again $\mu_1$. Let $\alpha^C$ repeat $a$ in every period. Then $\alpha^C$ is belief-based, single-price and confounding for some myopic pricing policy $\pi^*$, and, starting from belief $\mu_1$,
--   $$
--   W_T^{\alpha^C,\pi^*}(\mu_1)=T\cdot\Big(\mu_1\,\mathbb E[W\mid\phi_H,a,p]+(1-\mu_1)\,\mathbb E[W\mid\phi_L,a,p]\Big),
--   $$
--   $T$ times the one-period expected surplus of $(a,p)$. Applied to a one-period rule attaining $W^C(\mu_1)$, the payoff is $T\cdot W^C(\mu_1)$.
--
--   This is the step by which the proof of Theorem 1 realizes $W^C$ over any horizon.
--
--   **Formalization Note.** The page asserts the payoff $T\cdot W^C(\mu_1)$ for every $\mu_1$, using an optimal solution of the static problem (34) at $\delta=0$. Under the tie-break of Definition 1 the supremum defining $W^C(\mu_1)$ need not be attained: for $\phi_L=1/4$, $\phi_H=1/2$, $\mathcal P=[0,1]$, $\bar\rho_c=\bar\rho_0=1-p$, $\bar W_c=\bar W_0=(1-p)^2/2$, $\bar W_{\mathrm{out}}=10$ and $\mu_1=1/2$, the optimum of (34) leaves the seller indifferent between the target price and the unpromoted price $1/2$, which gives higher current surplus and is therefore the price selected. The statement therefore asserts the construction for any one-period rule, which yields $T\cdot W^C(\mu_1)$ whenever $W^C(\mu_1)$ is attained. The myopic pricing policy is required at every history, including those off the path.
-- source:
--   Gur, Macnamara, Morgenstern & Saban, Information Disclosure and Promotion Policy Design for Platforms, arXiv:1911.09256v5, p. OA–17 (PDF 51), proof of Theorem 1, "Existence of Optimal Confounding Promotion Policy"

import Mathlib
import Definitions.Def_ConfoundPromo_LongRun_Model

namespace ConfoundPromo.LongRun

open Finset

/-- "Existence of Optimal Confounding Promotion Policy" (p. OA–17), stated as its construction:
repeating a single-price one-period confounding rule a with myopic choice p in every period gives
a belief-based, confounding policy with a myopic pricing response and total surplus T times the
one-period surplus. (The printed "T · W^C(μ1) for every μ1" needs the sup in W^C to be attained,
which can fail under Definition 1's tie-break; see the Formalization Note.) -/
theorem optimal_confounding_policy (M : Market) (hM : M.Standing) (T : ℕ) (hT : 0 < T)
    (μ1 : ℝ) (hμ1 : μ1 ∈ Set.Icc (0 : ℝ) 1) (a : ℝ → Bool → ℝ) (p : ℝ)
    (ha : IsValidRule a) (hsingle : ∃ pbar ∈ M.price, ∀ q ∈ M.price, q ≠ pbar → ∀ b, a q b = 0)
    (hmy : IsMyopicChoice M μ1 a p) (hconf : IsConfoundingChoice M μ1 a p) :
    ∃ (α : Promo 1 T) (π : Pricing 1 T), α.IsValid ∧ (∀ t q b h, α t q b h = a q b) ∧
      IsBeliefBased M μ1 trivialSignal α ∧ IsSinglePrice M α ∧
      IsMyopic M μ1 trivialSignal α π ∧ IsConfounding M μ1 trivialSignal α π ∧
      surplusT M μ1 trivialSignal α π = T * expSurplus M μ1 a p := by sorry

end ConfoundPromo.LongRun
