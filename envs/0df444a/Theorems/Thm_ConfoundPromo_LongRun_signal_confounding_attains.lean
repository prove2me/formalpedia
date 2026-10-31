-- Prove2me | Theorems.Thm_ConfoundPromo_LongRun_signal_confounding_attains
-- name    : ConfoundPromo.LongRun.signal_confounding_attains
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-30T07:50:57.777584+00:00
-- url     : https://prove2.me/theorems/d49f19ca-83e0-4552-baa1-b8aebdd7a8cb
-- title:
--   Proof of Theorem 1, p. OA–17 (existence) — a two-signal mechanism and posterior-wise confounding myopic rules attaining co(W^C)(µ0)
-- statement:
--   Fix a market satisfying the standing assumptions (Assumptions 1 and 2) and a prior $\mu_0\in[0,1]$. Let $W^C(\mu)$ be the maximal one-period consumer surplus of a confounding promotion rule at belief $\mu$, as in (10), and $co(W^C)$ its concavification. Then there are
--
--   1. a signaling mechanism $\sigma$ with two signals $s\in\{1,2\}$, with signal probabilities $\mathbb P(s)=\mu_0\,\sigma(s\mid\phi_H)+(1-\mu_0)\,\sigma(s\mid\phi_L)$ and Bayes posteriors $\mu_1(s)$, and
--   2. for each posterior $\mu=\mu_1(s)$, a one-period promotion rule $a_\mu(p,\phi)\in[0,1]$ and a price $p_\mu$ that is a myopic choice against $a_\mu$ at belief $\mu$ (Definition 1, including the surplus tie-break) and is confounding: after either sale outcome the seller's posterior is again $\mu$,
--
--   such that the signal-averaged current expected consumer surplus equals the concavification:
--   $$
--   \sum_{s}\mathbb P(s)\Big(\mu_1(s)\,\mathbb E\big[W\mid\phi_H,a_{\mu_1(s)},p_{\mu_1(s)}\big]+(1-\mu_1(s))\,\mathbb E\big[W\mid\phi_L,a_{\mu_1(s)},p_{\mu_1(s)}\big]\Big)=co(W^C)(\mu_0).
--   $$
--
--   This is the static content of the existence half of Theorem 1: the paper combines an optimal signal (Kamenica–Gentzkow) with, at each posterior, a one-period confounding rule attaining $W^C$; repeating that rule every period yields average surplus exactly $co(W^C)(\mu_0)$ for every horizon $T$. The multi-period construction is the reduction of Theorem 1, part (ii), to this statement.
--
--   **Formalization Note.** The rule and price are indexed by the posterior value (functions $a:\mathbb R\to(\mathbb R\to\{H,L\}\to\mathbb R)$ and $p:\mathbb R\to\mathbb R$), so two signals with the same posterior use the same rule, as a belief-based policy must. The posterior of a signal of probability $0$ is Bayes' junk value $\mu_0$; such a signal carries no weight in the sum, but a confounding myopic choice is still required there. The equality presupposes that the supremum in $W^C$ is attained at the posteriors used, as in the paper's proof.
-- source:
--   Gur, Macnamara, Morgenstern & Saban, Information Disclosure and Promotion Policy Design for Platforms, arXiv:1911.09256v5, p. OA-17, proof of Theorem 1: 'Existence of Optimal Confounding Promotion Policy' and 'Existence of Optimal Signaling Mechanism' (combined, one-period form); Theorem 1, p. 19

import Mathlib
import Definitions.Def_ConfoundPromo_LongRun_Model

namespace ConfoundPromo.LongRun

open Finset

/-- Existence part of the proof of Theorem 1 (p. OA–17), one-period form: a two-signal mechanism
together with, at each of its posteriors, a one-period rule and a myopic price that keep the belief
fixed, whose signal-averaged current expected surplus equals co(W^C)(μ0). -/
theorem signal_confounding_attains (M : Market) (hM : M.Standing) (μ0 : ℝ)
    (hμ0 : μ0 ∈ Set.Icc (0 : ℝ) 1) :
    ∃ (sig : Signal 2) (a : ℝ → ℝ → Bool → ℝ) (p : ℝ → ℝ), sig.IsValid ∧
      (∀ s : Fin 2,
        IsValidRule (a (bayes μ0 (sig true s) (sig false s))) ∧
        IsMyopicChoice M (bayes μ0 (sig true s) (sig false s))
          (a (bayes μ0 (sig true s) (sig false s))) (p (bayes μ0 (sig true s) (sig false s))) ∧
        IsConfoundingChoice M (bayes μ0 (sig true s) (sig false s))
          (a (bayes μ0 (sig true s) (sig false s))) (p (bayes μ0 (sig true s) (sig false s)))) ∧
      ∑ s, (μ0 * sig true s + (1 - μ0) * sig false s) *
          expSurplus M (bayes μ0 (sig true s) (sig false s))
            (a (bayes μ0 (sig true s) (sig false s))) (p (bayes μ0 (sig true s) (sig false s)))
        = co (WC M) μ0 := by sorry

end ConfoundPromo.LongRun
