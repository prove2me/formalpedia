-- Prove2me | Theorems.Thm_FocusSetRB_lemma_3
-- name    : FocusSetRB.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:50.945991+00:00
-- url     : https://prove2.me/theorems/43c6b795-001a-495c-a96c-21fe93a2d70e
-- title:
--   Lemma 3, eq. (36), p.18 — the set-expansion policy satisfies Condition 1
-- statement:
--   Let $y^*$ be an optimal solution of (LP) whose policy $\bar\pi^*$ induces an aperiodic unichain (Assumption 1), let $0<\alpha<1$, $N\ge1$ and $k=\alpha N\in\mathbb N$. Consider a focus-set update obeying Algorithm 2, lines 2–5, and a rectifier obeying Algorithm 1's (4)–(5). For every system state $x$, every previous focus set $D_{\mathrm{prev}}$ and every focus set $D$ the update can choose from $(x,D_{\mathrm{prev}})$, let $\hat A\sim\bar\pi^*$ be the ideal actions, $A$ the rectified actions, and $D'=\{i\in D: A(i)=\hat A(i)\}$. Then
--
--   $$
--   \mathbb E\big[m(D\setminus D')\big]\le\frac1{\sqrt N}+\frac1N .
--   $$
--
--   In the paper's words: for any $t\ge0$ there is $D'_t\subseteq D_t$ on which $A_t=\hat A_t$, and $\mathbb E[m(D_t\setminus D'_t)\mid X_t,D_t]\le 1/\sqrt N+1/N$ almost surely. This is Condition 1 (majority conformity) with $K_{\mathrm{conf}}=1+1/\sqrt N$.
--
--   Differences from the source:
--   - generalization: the set-expansion policy of Algorithm 2 ("any set with the largest m(D_t)", uniform tie-breaking in lines 6–15) → every update kernel whose possible outputs obey lines 2–5 and every rectifier kernel whose possible outputs obey Algorithm 1's (4)–(5); reason: contains Algorithm 2 with every choice of maximizer and its uniform tie-breaking; p.10 says the analysis holds whenever lines 4–5 of Algorithm 1 are satisfied
--   - generalization: a.s., for the time-t pair (X_t, D_t) of the policy started at D_{−1} = ∅ → for every state x, every previous focus set D_prev and every D the update can choose from (x, D_prev); reason: every pair (X_t, D_t) of positive probability is of this form, so the pointwise bound implies the a.s. bound
--   - encoding: there exists D′_t ⊆ D_t with A_t(i) = Â_t(i) for i ∈ D′_t → D′_t = {i ∈ D_t : A_t(i) = Â_t(i)}; reason: every admissible D′_t is contained in this set, so m(D_t \ D′_t) is smallest for it; the existential holds iff it holds for this choice
--   - encoding: μ* is the stationary distribution of P_π̄* → μ*(s) := y*(s,0) + y*(s,1); reason: the paper states this identity on p.7; it is stationary by (2b) and (3) and is the unique stationary law under Assumption 1, so the same vector
--   - encoding: αN an integer, N arms → k : ℕ with (k : ℝ) = α·N and N ≥ 1; reason: the paper assumes αN is an integer (p.5); an N-armed problem has N ≥ 1
--   - encoding: P_π̄* induces an aperiodic unichain (a single recurrent class and a possibly empty set of transient states) → some state is recurrent, any two recurrent states reach each other, and every recurrent state has period 1; transient states are unconstrained; reason: the same property of a finite chain spelled out state by state; the period of a state is the gcd of its return times
--   - reading: D_t chosen based on X_t and D_{t−1}, actions based on X_t and D_t (Algorithm 1), "any set" in Algorithm 2 → the update and the rectifier are fixed kernels that do not depend on t; reason: Algorithm 1 names those as the inputs of the rule, and Appendix D (p.40) treats (S_t, A_t, X_t, D_t) as a finite-state Markov chain
--   - encoding: arms indexed by [N] = {1,…,N} → arms indexed by Fin N = {0,…,N−1}; reason: relabelling only
-- source:
--   Hong, Xie, Chen, Wang, Unichain and Aperiodicity are Sufficient for Asymptotic Optimality of Average-Reward Restless Bandits, arXiv:2402.05689v4, Lemma 3, eq. (36), p.18

import Mathlib
import Definitions.Def_FocusSetRB_LPFeasible
import Definitions.Def_FocusSetRB_IsAperiodicUnichain
import Definitions.Def_FocusSetRB_IsSetExpansionSelector

namespace FocusSetRB

/-- **Lemma 3 (Set-expansion policy satisfies Condition 1), eq. (36), p.18** (Hong, Xie, Chen, Wang, arXiv:2402.05689v4).
Consider the set-expansion policy (Algorithm 2). For any `t ≥ 0`, there exists a subset
`D'_t ⊆ D_t` such that `A_t(i) = Â_t(i)` for any `i ∈ D'_t`, and
`𝔼[m(D_t \ D'_t) | X_t, D_t] ≤ 1/√N + 1/N` a.s.

Here `y` is an optimal solution of (LP) whose policy `π̄*` (3) induces an aperiodic unichain
(Assumption 1, p.7, the paper's standing assumption).

**Formalization Note.** The set-expansion policy is any focus-set process whose update kernel
obeys Algorithm 2, lines 2–5 (`IsSetExpansionSelector`), and whose rectifier obeys Algorithm 1's
(4)–(5) (`IsRectifier`); Algorithm 2's lines 6–15 are one such rectifier (p.10). "a.s. given
`X_t, D_t`" is proved at **every** state `x`, every previous focus set `Dprev` and every `D` the
update can choose from `(x, Dprev)`, whatever the time step. Arms are `Fin N`, `N ≥ 1`,
`k = αN`. The subset `D'_t` is taken to be the largest admissible one,
`{i ∈ D_t : A_t(i) = Â_t(i)}`; any admissible `D'_t` is contained in it, so the existential and
this choice are equivalent. -/
theorem lemma_3 {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (M : SingleArmMDP S) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {y : S → Bool → ℝ} (hy : IsLPOptimal M α y) (hU : IsAperiodicUnichain (Ppi M y))
    {N k : ℕ} (hN : 1 ≤ N) (hk : (k : ℝ) = α * N)
    (sel : (Fin N → S) → Finset (Fin N) → Finset (Fin N) → ℝ)
    (hsel : IsSetExpansionSelector α y sel)
    (rect : (Fin N → S) → Finset (Fin N) → (Fin N → Bool) → (Fin N → Bool) → ℝ)
    (hrect : IsRectifier k rect)
    (x : Fin N → S) (Dprev D : Finset (Fin N)) (hD : 0 < sel x Dprev D) :
    ∑ Ahat, idealLaw y x Ahat *
        ∑ A, rect x D Ahat A * frac (D \ D.filter fun i => A i = Ahat i) ≤
      1 / Real.sqrt N + 1 / N := by sorry

end FocusSetRB
