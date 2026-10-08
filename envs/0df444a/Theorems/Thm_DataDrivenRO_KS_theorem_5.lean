-- Prove2me | Theorems.Thm_DataDrivenRO_KS_theorem_5
-- name    : DataDrivenRO.KS.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:45:46.564322+00:00
-- url     : https://prove2.me/theorems/3059d6fb-9072-477b-92e6-294156db2b05
-- title:
--   Theorem 5, p. 16 — 𝒰^I_ε is nonempty convex compact, δ*(v|𝒰^I_ε) dominates VaR^ℙ_ε(v) for every ℙ ∈ 𝒫^I, and δ*(v|𝒰^I_ε) is given by (19)
-- statement:
--   Fix $d$, $N\ge1$, a KS threshold $0<\Gamma<1$, points $\hat u^{(0)}_i<\hat u^{(1)}_i<\dots<\hat u^{(N+1)}_i$ for each coordinate $i$, and $0<\epsilon<1$. Let $\mathcal P^I$ be the product of the Kolmogorov–Smirnov confidence regions and $\mathcal U^I_\epsilon$ the set (18) (see the Setting). Then:
--
--   1. $\mathcal U^I_\epsilon$ is nonempty, convex and compact;
--   2. for every $v\in\mathbb R^d$ and every $\mathbb P\in\mathcal P^I$,
--   $$\mathrm{VaR}^{\mathbb P}_\epsilon(v)\le\delta^*(v\mid\mathcal U^I_\epsilon);$$
--   3. for every $v\in\mathbb R^d$, (19) holds:
--   $$\delta^*(v\mid\mathcal U^I_\epsilon)=\inf_{\lambda>0}\Big\{\lambda\log(1/\epsilon)+\lambda\sum_{i=1}^d\log\Big[\max\Big(\sum_{j=0}^{N+1}q^L_j(\Gamma)e^{v_i\hat u^{(j)}_i/\lambda},\ \sum_{j=0}^{N+1}q^R_j(\Gamma)e^{v_i\hat u^{(j)}_i/\lambda}\Big)\Big]\Big\}.$$
--
--   By Theorem 1 of the paper, for a nonempty convex compact set the inequality in 2 for every $v$ is equivalent to the set implying a probabilistic guarantee at level $\epsilon$ for $\mathbb P$. Since $\mathbb P^*\in\mathcal P^I$ with probability at least $1-\alpha$ over the sample (the coverage of the $d$ KS tests at level $1-\sqrt[d]{1-\alpha}$), this is the deterministic content of Theorem 5: with that probability the family $\{\mathcal U^I_\epsilon:0<\epsilon<1\}$ simultaneously implies a probabilistic guarantee for $\mathbb P^*$, and (19) gives its support function in closed form.
--
--   **Formalization Note** The guarantee is stated in the criterion form $\mathrm{VaR}\le\delta^*$ of Theorem 1(a); the coverage of the KS test, which rests on the distribution-free law of the KS statistic (tables), is cited and not formalized. The infimum in (19) is over $\lambda>0$ (the page's $\lambda\ge0$ has the same value) and is stated with `IsGLB`. Conclusion 1 rules out the junk value $0$ of the real `sSup` in `RobustMDP.Shared.supportFunction`. The order statistics are taken as data, ordered and inside the box (`Monotone (uhat i)`, ties allowed).
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 5, (18)–(19), p. 16 (proof EC.1.4, p. ec4)

import Mathlib
import Definitions.Def_DataDrivenRO_KS_Setting

open MeasureTheory

namespace DataDrivenRO.KS

theorem theorem_5 {d N : ℕ} (uhat : Fin d → Fin (N + 2) → ℝ) (Γ : ℝ)
    (hN : 0 < N) (hΓ0 : 0 < Γ) (hΓ1 : Γ < 1) (hmono : ∀ i, Monotone (uhat i))
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ((UI uhat Γ ε).Nonempty ∧ Convex ℝ (UI uhat Γ ε) ∧ IsCompact (UI uhat Γ ε)) ∧
    ∀ v : Fin d → ℝ,
      (∀ P ∈ productRegion uhat Γ,
        VaR P ε v ≤ RobustMDP.Shared.supportFunction (UI uhat Γ ε) v) ∧
      IsGLB (boundKS uhat Γ ε v '' Set.Ioi 0)
        (RobustMDP.Shared.supportFunction (UI uhat Γ ε) v) := by sorry

end DataDrivenRO.KS
