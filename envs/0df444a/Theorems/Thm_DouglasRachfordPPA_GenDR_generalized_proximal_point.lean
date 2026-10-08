-- Prove2me | Theorems.Thm_DouglasRachfordPPA_GenDR_generalized_proximal_point
-- name    : DouglasRachfordPPA.GenDR.generalized_proximal_point
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T14:04:08.737985+00:00
-- url     : https://prove2.me/theorems/6a17630b-f7ce-46a4-a9ff-b7868396ab96
-- title:
--   Theorem 3 — the generalized proximal point algorithm converges weakly to a zero, or is unbounded
-- statement:
--   Let $\mathcal H$ be a real Hilbert space and $T$ a maximal monotone operator on $\mathcal H$. Let $\{c_k\}$, $\{\rho_k\}$, $\{\varepsilon_k\}$ be real sequences and $\{z^k\}$, $\{w^k\}$ sequences in $\mathcal H$ ($k\ge0$) such that
--   $$z^{k+1}=(1-\rho_k)z^k+\rho_k w^k,\qquad \|w^k-(I+c_kT)^{-1}(z^k)\|\le\varepsilon_k\qquad\forall k\ge0,$$
--   where $\varepsilon_k\ge0$, $\sum_{k=0}^\infty\varepsilon_k<\infty$, $\inf_k\rho_k>0$, $\sup_k\rho_k<2$ and $\inf_k c_k>0$. Then:
--
--   1. if $T$ has a zero, $\{z^k\}$ converges weakly to a zero of $T$;
--   2. if $T$ has no zero, $\{z^k\}$ is unbounded.
--
--   The theorem combines Rockafellar's inexact proximal point algorithm (variable stepsizes $c_k$) with the over/under-relaxation of Gol'shtein and Tret'yakov, in a general Hilbert space and including the case without zeros. Theorem 7 is obtained by applying it to the splitting operator.
--
--   **Formalization Note** The printed statement has two slips, corrected here: it reads $z^{k+1}=(1-\rho_k)z^k+(1-\rho_k)w^k$ where the text before it (p. 9) and the proof (pp. 11, 14) use $\rho_k w^k$, and it writes $(I+cT)^{-1}$ where the proof uses $(I+c_kT)^{-1}$ ($Q_k=I-J_{c_kT}$, p. 11). The resolvent $(I+c_kT)^{-1}$ is a map $J_k:\mathcal H\to\mathcal H$ with $\tfrac1{c_k}(x-J_k x)\in T(J_kx)$ for all $x$ (unique by Corollary 2.2). The conditions $\inf\rho_k>0$, $\sup\rho_k<2$ are encoded as $\exists\,\rho_1,\rho_2$ with $0<\rho_1\le\rho_k\le\rho_2<2$, and $\inf c_k>0$ as $\exists\,c_0>0$ with $c_0\le c_k$ for all $k$; these are equivalent to the page and imply the page's $\rho_k,c_k\ge0$. Weak convergence is $\langle z^k,y\rangle\to\langle z^*,y\rangle$ for all $y$; unboundedness is "the range of $k\mapsto z^k$ is not bounded". Sequences are indexed from $k=0$.
-- source:
--   Eckstein and Bertsekas, On the Douglas–Rachford Splitting Method and the Proximal Point Algorithm for Maximal Monotone Operators, MIT LIDS-P-1919 (October 1989), p. 10, Theorem 3 (slips corrected from p. 9 and the proof, pp. 11, 14)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence

open InnerProductSpace ThreeOpSplitting.Convergence

namespace DouglasRachfordPPA.GenDR

/-- Theorem 3 (generalized proximal point algorithm), with the printed slips corrected:
`z (k+1) = (1 - ρ k) z k + ρ k w k` and `‖w k - J_{c_k T}(z k)‖ ≤ ε k`. The resolvent
`J_{c_k T}` is the map `J k` with `IsResolvent (c k) T (J k)`. -/
theorem generalized_proximal_point
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H → Set H) (hT : IsMaximalMonotone T)
    (c ρ ε : ℕ → ℝ) (J : ℕ → H → H) (hJ : ∀ k, IsResolvent (c k) T (J k))
    (z w : ℕ → H)
    (hz : ∀ k, z (k + 1) = (1 - ρ k) • z k + ρ k • w k)
    (hw : ∀ k, ‖w k - J k (z k)‖ ≤ ε k)
    (hε_nonneg : ∀ k, 0 ≤ ε k) (hε_sum : Summable ε)
    (hρ : ∃ ρ₁ ρ₂ : ℝ, 0 < ρ₁ ∧ ρ₂ < 2 ∧ ∀ k, ρ₁ ≤ ρ k ∧ ρ k ≤ ρ₂)
    (hc : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ k, c₀ ≤ c k) :
    ((zer T).Nonempty → ∃ zs ∈ zer T, WeakTendsto z zs) ∧
    (zer T = ∅ → ¬ Bornology.IsBounded (Set.range z)) := by sorry

end DouglasRachfordPPA.GenDR
