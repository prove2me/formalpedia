-- Prove2me | Theorems.Thm_EngageInfo_proposition_1
-- name    : EngageInfo.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:20:35.915015+00:00
-- url     : https://prove2.me/theorems/bf48bd78-bba5-4fd3-9a50-fd42573730a3
-- title:
--   Proposition 1 — the seller-optimal posteriors under observable engagement (corrected: ties at $\bar e=\alpha_0\Theta$ and $\bar e=\Theta$)
-- statement:
--   Assume $\theta_H>\theta_L>c\ge0$, $\bar e>k>0$ and $\alpha_1<\alpha_{\bar e}$, write $m=\max\{\alpha_0,\alpha_1\}$, and let the prior be $\alpha^0\in(0,1)$. The seller chooses a design to maximize $W$; a design is described by the posteriors $(\alpha_l,\alpha_h)$ it induces.
--
--   **(a) The posteriors of Proposition 1 are optimal.**
--
--   1. If $\bar e<\alpha_0\Theta$: some optimal design induces $(\alpha_l,\alpha_h)=(0,1)$ (full information).
--   2. If $\alpha_0\Theta\le\bar e\le\Theta$: for $\alpha^0<m$ some optimal design induces $(0,m)$; for $\alpha^0>m$ some optimal design induces $(m,1)$.
--   3. If $\bar e>\Theta$: for $\alpha^0<m$ some optimal design induces $(0,m)$; for $m<\alpha^0<\alpha_{\bar e}$ every uninformative design (posteriors $\alpha_l=\alpha_h=\alpha^0$) is optimal; for $\alpha^0>\alpha_{\bar e}$ some optimal design induces $(\alpha_{\bar e},1)$.
--
--   **(b) Except at $\bar e=\alpha_0\Theta$, and at $\bar e=\Theta$ with $\alpha^0>m$, they are the only optimal posteriors.** If $\bar e<\alpha_0\Theta$, every optimal design induces $(0,1)$. If $\alpha_0\Theta<\bar e\le\Theta$ and $\alpha^0<m$, every optimal design induces $(0,m)$. If $\alpha_0\Theta<\bar e<\Theta$ and $\alpha^0>m$, every optimal design induces $(m,1)$. If $\bar e>\Theta$, every optimal design induces $(0,m)$ when $\alpha^0<m$ and $(\alpha_{\bar e},1)$ when $\alpha^0>\alpha_{\bar e}$, and when $m<\alpha^0<\alpha_{\bar e}$ every optimal design has both posteriors in $[m,\alpha_{\bar e}]$.
--
--   **(c) At $\bar e=\Theta$** and $m<\alpha^0\le\alpha_{\bar e}$, every uninformative design is optimal.
--
--   With the paper's tie-break (the prior is chosen whenever it is as good as another design), (a)–(c) say the selected posteriors are exactly the printed ones whenever $\bar e\notin\{\alpha_0\Theta,\Theta\}$. When the prior is low the seller tells the truth in state $H$ but sometimes sends $h$ in state $L$ (it exaggerates); when the prior is high it does the reverse (it downplays). Both keep the posterior in the region where the customer engages.
--
--   **Formalization Note** $v^*$ is the seller-preferred equilibrium payoff of the stated game, designs are pairs $(\pi_h,\pi_l)\in[0,1]^2$ with $\pi_h+\pi_l\ge1$, and the posterior after a probability-zero signal is the prior. As printed, the proposition makes no claim at $\alpha^0=m$ or $\alpha^0=\alpha_{\bar e}$, and neither does this statement.
--
--   Differences from the source:
--   - correction: "the posterior beliefs under the optimal information design for the seller are given by" the printed pairs on the closed range ē ∈ [α₀Θ, Θ], with the prior selected only when it ties (p.6) → (a) the printed pairs are optimal on the full printed ranges; (b) uniqueness except at ē = α₀Θ and at ē = Θ with α⁰ > m (at ē = Θ with α⁰ < m the pair (0, m) is still the unique optimum); (c) at ē = Θ and m < α⁰ ≤ α_ē the uninformative design is optimal; reason: at the boundaries the optimum is not unique: θH = 10, θL = 5, c = 1, k = 1/2, ē = 5 = Θ, α⁰ = 1/2: the prior and (4/9, 1) both earn 9, so the tie-break selects the prior, not the printed pair; with ē = 20/9 = α₀Θ, α⁰ = 1/4: (0, 4/9) and (0, 1) both earn 21/4
--   - reading: "the posterior beliefs under the optimal information design … are given by", with the tie-break of p.6 → some optimal design induces the printed pair, and every optimal design does (in (iii)'s middle range: uninformative designs are optimal and every optimal design keeps both posteriors in [m, α_ē]); reason: these are exactly the conditions under which the tie-break of p.6 selects the printed posteriors
--   - reading: "the seller's equilibrium expected payoff" v∗(α), with "the equilibrium" called unique (p.8) → v∗(α) = the maximum of the seller's payoffs over all pure subgame-perfect equilibria at belief α (seller-preferred equilibrium); reason: at α ∈ {α₀, α₁, α_ē} the subgame has several SPE with different seller payoffs; the closed interval of Lemma 1 and the values of (6) there are those of the seller-preferred SPE
--   - reading: the customer purchases in state ω (rule left implicit) → the customer buys iff θ_ω + e − p ≥ 0, i.e. also at indifference; reason: without purchase at indifference the seller has no best price and no SPE exists
--   - encoding: engagement e ∈ {0, ē}; SPE of the engagement–pricing subgame → engagement as Bool (true ↦ ē, false ↦ 0); pure-strategy SPE via the published CollabProject.TimeDep.SequentialGame.IsSPNE, the seller best-responding after each engagement level; reason: the §3 analysis is in pure strategies with the seller observing e; relabelling only
--   - encoding: signals (π_h, π_l) with π_h ≥ 1 − π_l; posteriors by Bayes' rule → pairs (π_h, π_l) ∈ [0,1]² with π_h + π_l ≥ 1; the posterior after a probability-zero signal is set to the prior α⁰; reason: Bayes' rule leaves a null signal's posterior undefined; it has weight 0 in every expectation, so no value changes
-- source:
--   Guo, Designing Information to Engage Customers, Management Science (2025), doi:10.1287/mnsc.2022.03503, Proposition 1, p.13; tie-break, p.6; standing assumption α₁ < α_ē, p.10

import Mathlib
import Definitions.Def_EngageInfo_Params
import Definitions.Def_EngageInfo_vstar
import Definitions.Def_EngageInfo_designs
import Definitions.Def_EngageInfo_designValue

namespace EngageInfo

/-- **Proposition 1: the seller-optimal information design under observable engagement.**
Guo, *Designing Information to Engage Customers*, Management Science (2025), Proposition 1, p.13:
"Under observable customer engagement, the posterior beliefs under the optimal information design
for the seller are given by: (i) When ē < α₀Θ, α∗l = 0 and α∗h = 1 for all α⁰ ∈ (0, 1); (ii) When
ē ∈ [α₀Θ, Θ], α∗l = 0 and α∗h = max{α₀, α₁} for α⁰ < max{α₀, α₁}, and α∗l = max{α₀, α₁} and α∗h = 1
for α⁰ > max{α₀, α₁}; (iii) When ē > Θ, α∗l = 0 and α∗h = max{α₀, α₁} for α⁰ < max{α₀, α₁},
α∗l = α∗h = α⁰ for α⁰ ∈ (max{α₀, α₁}, αē), and α∗l = αē and α∗h = 1 for α⁰ > αē."
Tie-break, p.6: "We assume that the prior is selected (i.e., αh = αl = α⁰) when it is as optimal as
some other information structure for the seller." Standing assumption, p.10: `α₁ < α_ē`.

Write `m = max{α₀, α₁}`. For all parameters with `α₁ < α_ē` and every prior `α⁰ ∈ (0, 1)`:

(a) the printed posteriors are optimal on the full printed ranges:
  (i) if `ē < α₀Θ`, some optimal design induces `(α_l, α_h) = (0, 1)`;
  (ii) if `α₀Θ ≤ ē ≤ Θ`: for `α⁰ < m` some optimal design induces `(0, m)`, and for `α⁰ > m` some
  optimal design induces `(m, 1)`;
  (iii) if `ē > Θ`: for `α⁰ < m` some optimal design induces `(0, m)`; for `m < α⁰ < α_ē` every
  uninformative design is optimal; for `α⁰ > α_ē` some optimal design induces `(α_ē, 1)`.

(b) they are the only optimal posteriors except at `ē = α₀Θ`, and at `ē = Θ` for `α⁰ > m`: in each
case of (a) except (iii)'s middle range, **every** optimal design induces the printed pair (so no
uninformative design is optimal and the tie-break plays no role); this includes `ē = Θ` with
`α⁰ < m`; in (iii)'s middle range every optimal design has both posteriors in `[m, α_ē]` (and by
(a) the uninformative designs are optimal, so the tie-break selects the prior, as printed).

(c) correction at `ē = Θ`: for `m < α⁰ ≤ α_ē` every uninformative design is optimal (so the
tie-break selects the prior there, not the printed `(m, 1)`).

**Formalization Note** `v*` is the seller-preferred SPE payoff of the stated game (`vstar`), designs
are pairs `(π_h, π_l) ∈ [0,1]²` with `π_h + π_l ≥ 1`, and the posterior of a probability-zero signal
is the prior. At `ē = α₀Θ` (both ranges of α⁰) and at `ē = Θ` with `α⁰ > m` the printed pair is optimal but
not the only optimal design
(e.g. `θ_H = 10, θ_L = 5, c = 1, k = 1/2`: with `ē = Θ = 5`, `α⁰ = 1/2`, the prior and `(4/9, 1)`
both earn 9; with `ē = 20/9 = α₀Θ`, `α⁰ = 1/4`, `(0, 4/9)` and `(0, 1)` both earn 21/4). The
printed ranges leave `α⁰ = m` and `α⁰ = α_ē` out, and so does this statement. -/
theorem proposition_1 (M : Params) (hα : M.α₁ < M.αbar) (a0 : ℝ) (ha0 : a0 ∈ Set.Ioo (0 : ℝ) 1) :
    -- (a) the printed posteriors are optimal
    ((M.ebar < M.α₀ * M.Θ → ∃ π, IsOptimal M a0 π ∧ Induces a0 π 0 1) ∧
      (M.α₀ * M.Θ ≤ M.ebar ∧ M.ebar ≤ M.Θ →
        (a0 < M.m → ∃ π, IsOptimal M a0 π ∧ Induces a0 π 0 M.m) ∧
        (M.m < a0 → ∃ π, IsOptimal M a0 π ∧ Induces a0 π M.m 1)) ∧
      (M.Θ < M.ebar →
        (a0 < M.m → ∃ π, IsOptimal M a0 π ∧ Induces a0 π 0 M.m) ∧
        (M.m < a0 → a0 < M.αbar → ∀ π, IsUninformative π → IsOptimal M a0 π) ∧
        (M.αbar < a0 → ∃ π, IsOptimal M a0 π ∧ Induces a0 π M.αbar 1))) ∧
    -- (b) uniqueness, except at ē = α₀Θ and at ē = Θ with α⁰ > m
    ((M.ebar < M.α₀ * M.Θ → ∀ π, IsOptimal M a0 π → Induces a0 π 0 1) ∧
      (M.α₀ * M.Θ < M.ebar ∧ M.ebar ≤ M.Θ →
        a0 < M.m → ∀ π, IsOptimal M a0 π → Induces a0 π 0 M.m) ∧
      (M.α₀ * M.Θ < M.ebar ∧ M.ebar < M.Θ →
        M.m < a0 → ∀ π, IsOptimal M a0 π → Induces a0 π M.m 1) ∧
      (M.Θ < M.ebar →
        (a0 < M.m → ∀ π, IsOptimal M a0 π → Induces a0 π 0 M.m) ∧
        (M.m < a0 → a0 < M.αbar → ∀ π, IsOptimal M a0 π →
          postL a0 π ∈ Set.Icc M.m M.αbar ∧ postH a0 π ∈ Set.Icc M.m M.αbar) ∧
        (M.αbar < a0 → ∀ π, IsOptimal M a0 π → Induces a0 π M.αbar 1))) ∧
    -- (c) correction at ē = Θ: the prior is optimal on (m, α_ē]
    (M.ebar = M.Θ → M.m < a0 → a0 ≤ M.αbar →
      ∀ π, IsUninformative π → IsOptimal M a0 π) := by sorry

end EngageInfo
