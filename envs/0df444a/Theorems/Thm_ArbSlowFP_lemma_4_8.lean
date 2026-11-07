-- Prove2me | Theorems.Thm_ArbSlowFP_lemma_4_8
-- name    : ArbSlowFP.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:52:15.190966+00:00
-- url     : https://prove2.me/theorems/79bcfbb3-4bbd-49d8-8529-b35295be055f
-- title:
--   Lemma 4.8 — the gap at all integer times: $c_kt^{-1/k}(1+o(1))$
-- statement:
--   Let an order-$k$ clock have count table $C$, score table $R$ and entry action $b$. Fix a phase $Q\ge Q_k$, take $f=r(Q)$, let $\beta$ realize the priority rule as in Lemma 4.6, and let $\hat A$ be the game of Lemma 4.7. Put
--   $$L=(\mathbf 1^\top C)_{k-1}>0,\quad \xi=R_{b,k-1}>0,\quad a=\frac L{k!},\quad b_*=\frac\xi{(k-1)!},\quad c_k=2b_*a^{-(k-1)/k}>0 .$$
--   Then for every run from zero counts with the setup action played first,
--   $$\mathrm{Gap}_{\hat A}(z_t/t,z_t/t)=c_kt^{-1/k}(1+o(1))$$
--   as $t\to\infty$ over all integers.
--
--   This gives the rate of the main theorem from the clock's tables.
--
--   **Formalization Note** $o(1)$ is the limit of the ratio to $c_kt^{-1/k}$ being $1$. The biased process is a hypothesis on $\beta$, satisfied by Lemma 4.6's $\beta$, and the priority run is any sequence satisfying the process from $f$. Empirical strategies are written for each player's own counts, which agree by Lemma 4.7.
--
--   Differences from the source:
--   - encoding: "Apply Lemmas 4.6 and 4.7" → for every β such that the priority trajectory from f has unique maximizers in the (f+β)-process; reason: this is the property Lemma 4.6 gives; the leading terms do not depend on which such β is used
--   - encoding: run of (3) with both players choosing the setup action in round 0 → every sequence of plays satisfying (3) with those first plays, together with a clause that one exists; reason: the plays are the data and ties at t = 0 are free; the statement does not assume uniqueness of the run
-- source:
--   Abernethy, Lazarsfeld, Wibisono, Arbitrarily Slow Polynomial Convergence of Fictitious Play, arXiv:2610.08768 (version of November 3, 2026, sha256 977c34b6…), p.30, Lemma 4.8, eq. (23)

import Mathlib
import Definitions.Def_ArbSlowFP_IsFPRun
import Definitions.Def_ArbSlowFP_IsClock
import Definitions.Def_ArbSlowFP_setupGame

open Matrix Filter Topology

namespace ArbSlowFP

/-- Lemma 4.8, p.30 (arXiv:2610.08768, version of November 3, 2026, sha256 977c34b6…). Let an order-k
clock be given and apply Lemmas 4.6 and 4.7 starting at a fixed phase `Q ≥ Q_k`: `f = r(Q)`, `β` realizes
the priority rule, and the game is (22). With `L = (1⊤C)_{k-1} > 0`, `ξ = R_{b,k-1} > 0`, `a = L/k!`,
`b∗ = ξ/(k-1)!` and `c_k = 2b∗a^{-(k-1)/k} > 0`, the gap of every run is `c_k t^{-1/k}(1 + o(1))` as `t → ∞`
over all integers.

**Formalization Note.** `o(1)` is the limit `1` of the ratio. -/
theorem lemma_4_8 {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (d : ClockData k ι) (hd : IsClock d) (Q : ℕ) (hQ : d.Q ≤ Q)
    (β : ι → ℚ) (w : ℕ → ι) (hw : IsPriorityRun d.A d.rank (d.r Q) w)
    (hβ : ∀ t, IsUniqueMax (procScore d.A (d.r Q + β) w t) (w t))
    (ck : ℝ)
    (hck : ck = 2 * ((lastCoef (d.R d.b) : ℝ) / ((k - 1).factorial : ℝ)) *
      ((lastCoef ((1 : ι → ℚ) ᵥ* d.C) : ℝ) / (k.factorial : ℝ)) ^
        (-(((k : ℝ) - 1) / (k : ℝ)))) :
    0 < lastCoef ((1 : ι → ℚ) ᵥ* d.C) ∧ 0 < lastCoef (d.R d.b) ∧ 0 < ck ∧
    ∀ i j, IsFPRun (toReal (setupGame d.A (d.r Q + β))) i j → i 0 = none → j 0 = none →
      Tendsto (fun t : ℕ =>
          gap (toReal (setupGame d.A (d.r Q + β))) (empirical i t) (empirical j t) /
            (ck * (t : ℝ) ^ (-(1 / (k : ℝ))))) atTop (𝓝 1) := by sorry

end ArbSlowFP
