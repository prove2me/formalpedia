-- Prove2me | Theorems.Thm_EffHorizonProphet_Supplement_theorem_8
-- name    : EffHorizonProphet.Supplement.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:04:50.635993+00:00
-- url     : https://prove2.me/theorems/d434fa50-793a-4a58-b60a-9a022301488f
-- title:
--   Theorem 8 — the 1/2 barrier for the DP policy and every stopping rule as $\tilde\gamma\uparrow1$, $S\to\infty$, $\tilde\gamma^S\to0$
-- statement:
--   Consider a common decay factor $\tilde\gamma\in[0,1)$ and $S$ phases of equal length, with rewards $X_i=\tilde\gamma^{s-1}Y_i$ for $i\in T_s$ and $Y_1,\dots,Y_n$ i.i.d. from an admissible base law $D$. For a policy $\tau$ write
--   $$\mathrm{CR}_n(\tau)=\inf_{D\in\mathcal D}\frac{\mathbb E_D[X_\tau]}{\mathbb E_D[\max_{i\le n}X_i]}.$$
--   In the joint limit $\tilde\gamma\uparrow1$, $S\to\infty$, $\tilde\gamma^S\to0$, the dynamic-programming policy $\tau_{\mathrm{DP}}$ (which uses the values $V_i$ of the law $D$) satisfies
--   $$\limsup_{\tilde\gamma\uparrow1,\,S\to\infty,\,\tilde\gamma^S\to0}\ \limsup_{n\to\infty}\mathrm{CR}_n(\tau_{\mathrm{DP}})\le\frac12,$$
--   and consequently the same double limsup is at most $\tfrac12$ for every stopping policy $\tau$.
--
--   Precisely: for every $u>1/2$, for all $(\tilde\gamma,S)$ far enough in the joint limit and all large horizons, there is one admissible law $D$ on which both $\tau_{\mathrm{DP}}$ and every stopping rule earn at most $u\,\mathbb E_D[\max_iX_i]$.
--
--   So decaying rewards can make the i.i.d. stopping problem as hard as the non-identical prophet problem, whose classical barrier is also $1/2$.
--
--   Differences from the source:
--   - generalization: phases of equal length $n/S$ with $S\mid n$ and $n\to\infty$ → for each $S\ge1$ any sequence of profiles $L_S(t)$ with $\sum_sL_S(t)(s)\to\infty$ and $L_S(t)(s)/\sum_{s'}L_S(t)(s')\to1/S$; reason: this is the reading "(or asymptotically $n_s/n\to1/S$)" of p.3, and it contains the printed case $L_S(t)\equiv t$
--   - generalization: a stopping rule is a stopping time for $\sigma(Y_1,\dots,Y_i)$ (A.5, p.33; A.10, p.50) → a stopping time for the stage pairs $(Y_j,U_j)_{j\le i}$ with independent uniform coins $U_j$, so randomized rules are included; reason: the class of rules is larger, so the upper bound for it contains the paper's bound for every non-randomized rule
--   - generalization: for every stopping policy $\tau$, $\limsup\limsup_n\mathrm{CR}_n(\tau)\le\frac12$ (one $\tau$ at a time, $\mathrm{CR}_n$ an infimum over $D$) → one hard admissible law $D$ (for each $u$, $(\tilde\gamma,S)$ and horizon) on which every stopping rule earns at most $u\,\mathbb E_D[\max_iX_i]$; reason: $\exists D\,\forall\tau$ implies $\forall\tau\,\exists D$, so it gives the page's bound for each $\tau$ and also covers rules chosen knowing $D$; A.5 proves exactly this (the DP rule of the hard law dominates every rule)
--   - encoding: the joint limit $\tilde\gamma\uparrow1$, $S\to\infty$, $\tilde\gamma^S\to0$, with $\tilde\gamma\in[0,1)$ → the filter $(\mathcal N_{<}(1)\times\mathrm{atTop})\sqcap\mathrm{comap}(\tilde\gamma^S)\,\mathcal N(0)$ on $(\tilde\gamma,S)$; reason: it is that joint limit; it forces $0<\tilde\gamma<1$ eventually, and a sanity lemma shows it is not empty
--   - encoding: $\limsup\limsup_{n}\mathrm{CR}_n(\cdot)\le\frac12$ for $\tau_{\mathrm{DP}}$ and for every $\tau$ → for every $u>\frac12$, eventually in the joint limit, eventually in $n$, some admissible $D$ has $\mathbb E_D[X_{\tau}]\le u\,\mathbb E_D[\max_iX_i]$ for $\tau=\tau_{\mathrm{DP}}(D)$ and for every stopping rule $\tau$; reason: the same statement, since $\mathrm{CR}_n$ is an infimum over $D$, $u$ is arbitrary and $\mathbb E_D[\max_iX_i]>0$; it avoids the junk values of a real limsup
--   - encoding: a stopping rule takes values in $\{1,\dots,n\}$ (A.5) or $\{1,\dots,n+1\}$ (p.3), stages from $1$ → values in $\{0,\dots,n\}$, with $n$ meaning "never stop" (payoff $0$); reason: a relabelling; never stopping is the paper's $n+1$
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Theorem 8, p.11; proof in A.5, pp.31–34

import Mathlib
import Definitions.Def_EffHorizonProphet_IsAdmissible
import Definitions.Def_EffHorizonProphet_IsEqualProfile
import Definitions.Def_EffHorizonProphet_prophet
import Definitions.Def_EffHorizonProphet_Supplement_jointFilter
import Definitions.Def_EffHorizonProphet_Supplement_IsStoppingRule
import Definitions.Def_EffHorizonProphet_Supplement_stopReward
import Definitions.Def_EffHorizonProphet_Supplement_dpRule

open MeasureTheory Filter

namespace EffHorizonProphet.Supplement

/-- **Theorem 8** (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), p.11; proof in A.5, pp.31–34): with a common decay factor
`γ̃ ∈ [0, 1)` and equal-length phases, in the joint limit `γ̃ ↑ 1, S → ∞, γ̃^S → 0`,
`limsup limsup_{n→∞} CR_n(τ_DP) ≤ 1/2`, and consequently `limsup limsup_{n→∞} CR_n(τ) ≤ 1/2` for
every stopping policy `τ`.

**Formalization Note** "double limsup ≤ 1/2" is stated as: for every `u > 1/2`, eventually in the
joint filter, eventually in `n`, some admissible law `D` has `E_D[X_τ] ≤ u · E_D[max_i X_i]` both for
the DP rule of `D` and for every stopping rule. Since `u` is arbitrary this is the double limsup of
`CR_n = inf_D`. Phases are `0`-based and `L S t` is the phase profile of horizon `t` with `S`
phases, any asymptotically equal profile (`L S t = fun _ => t`, `n = S t`, is the printed case).
Stopping rules may use the independent coins (randomized rules). -/
theorem theorem_8 (L : (S : ℕ) → ℕ → Fin S → ℕ)
    (hL : ∀ S, 1 ≤ S → IsEqualProfile (L S)) {u : ℝ} (hu : 1 / 2 < u) :
    ∀ᶠ p in jointFilter, ∀ᶠ t in atTop, ∃ D : Measure ℝ, IsAdmissible D ∧
      stopReward p.1 (L p.2 t) D (dpRule p.1 (L p.2 t) D) ≤
        u * prophet p.1 (L p.2 t) D ∧
      ∀ τ, IsStoppingRule τ →
        stopReward p.1 (L p.2 t) D τ ≤ u * prophet p.1 (L p.2 t) D := by sorry

end EffHorizonProphet.Supplement
