-- Prove2me | Theorems.Thm_ConvexSDDP_Stoch_lemma_5_4
-- name    : ConvexSDDP.Stoch.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:56:39.047996+00:00
-- url     : https://prove2.me/theorems/3a30d032-ec63-4e7d-b781-31a25f0f5ca1
-- title:
--   Lemma 5.4, p. 26 — predictably selected terms of an i.i.d. sequence are i.i.d. with the same law
-- statement:
--   Let $(w^k)_{k\in\mathbb N}$ be a $\{0,1\}$-valued process adapted to a filtration $(\mathcal F_k)_{k\in\mathbb N}$, such that almost surely infinitely many $w^k$ equal $1$. Let $(y^k)_{k\in\mathbb N}$ be an i.i.d. sequence of discrete random variables. Put
--   $$\mathcal B_k=\sigma\big(\mathcal F_k\cup\sigma(y^1,\dots,y^{k-1})\big)$$
--   and assume that $y^k$ is independent of $\mathcal B_k$ for every $k$. Let $k(0)=0$ and $k(j)=\min\{l>k(j-1): w^l=1\}$ for $j>0$, and $z^j=y^{k(j)}$. Then $(z^j)_{j\ge1}$ is an i.i.d. sequence, each $z^j$ having the law of $y^0$.
--
--   This optional-skipping statement is applied in the proof of Theorem 3.1 (p. 21) to the selections $\tilde y^k_n$ along the iterations at which the approximation at $n$ is still $\varepsilon$-inexact.
--
--   **Formalization Note** "Discrete" is read as taking values in a countable type with the discrete σ-algebra. The Lean index $j$ of $z_j$ is the page's $z^{j+1}$, and $k(j+1)$ is the $j$-th (from $0$) index $l>0$ with $w^l=1$ (`Nat.nth`); $l=0$ is excluded because $k(0)=0$. On the null event where $w$ has finitely many ones, `Nat.nth` returns $0$; independence and laws are almost-sure notions, so this does not affect the statement.
-- source:
--   Girardeau, Leclère & Philpott, On the Convergence of Decomposition Methods for Multistage Stochastic Convex Programs, author's version hal-01208295v1, p. 26, Lemma 5.4

import Mathlib
open MeasureTheory ProbabilityTheory

namespace ConvexSDDP.Stoch

theorem lemma_5_4 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Fk : ℕ → MeasurableSpace Ω) (hFmono : Monotone Fk) (hFle : ∀ k, Fk k ≤ mΩ)
    (w : ℕ → Ω → Bool) (hw : ∀ k, Measurable[Fk k] (w k))
    (hinf : ∀ᵐ ω ∂P, Set.Infinite {l | w l ω = true})
    {β : Type*} [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]
    (y : ℕ → Ω → β) (hy : ∀ k, Measurable (y k))
    (hiid : iIndepFun y P ∧ ∀ k, IdentDistrib (y k) (y 0) P P)
    (hB : ∀ k, Indep (MeasurableSpace.comap (y k) inferInstance)
      (Fk k ⊔ ⨆ j ∈ Finset.Ico 1 k, MeasurableSpace.comap (y j) inferInstance) P) :
    iIndepFun (fun j ω => y (Nat.nth (fun l => 0 < l ∧ w l ω = true) j) ω) P ∧
      ∀ j, IdentDistrib (fun ω => y (Nat.nth (fun l => 0 < l ∧ w l ω = true) j) ω)
        (y 0) P P := by sorry

end ConvexSDDP.Stoch
