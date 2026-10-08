-- Prove2me | Theorems.Thm_DouglasRachfordPPA_GenDR_generalized_douglas_rachford_convergence
-- name    : DouglasRachfordPPA.GenDR.generalized_douglas_rachford_convergence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T14:23:50.848468+00:00
-- url     : https://prove2.me/theorems/ff90bd52-e2fb-40e9-8e16-6b26dc70e717
-- title:
--   Theorem 7 — generalized Douglas–Rachford splitting converges weakly if $A+B$ has a zero, else is unbounded
-- statement:
--   Let $\mathcal H$ be a real Hilbert space, $\lambda>0$, and $A,B$ maximal monotone operators on $\mathcal H$ with resolvents $J_{\lambda A},J_{\lambda B}:\mathcal H\to\mathcal H$. Let $\{z^k\}_{k\ge0}$, $\{u^k\}_{k\ge0}$, $\{v^k\}_{k\ge1}$ be sequences in $\mathcal H$ and $\{\alpha_k\},\{\beta_k\}\subseteq[0,\infty)$, $\{\rho_k\}$ real sequences ($k\ge0$) such that
--   $$\begin{aligned}
--   \|u^k-J_{\lambda B}(z^k)\|&\le\beta_k &&\forall k\ge0 &&\text{(T1)}\\
--   \|v^{k+1}-J_{\lambda A}(2u^k-z^k)\|&\le\alpha_k &&\forall k\ge0 &&\text{(T2)}\\
--   z^{k+1}&=z^k+\rho_k(v^{k+1}-u^k) &&\forall k\ge0 &&\text{(T3)}
--   \end{aligned}$$
--   and
--   $$\sum_{k=0}^\infty\alpha_k<\infty,\qquad\sum_{k=0}^\infty\beta_k<\infty,\qquad 0<\inf_{k\ge0}\rho_k\le\sup_{k\ge0}\rho_k<2 .$$
--   Then:
--
--   1. if $\operatorname{zer}(A+B)\neq\emptyset$, $\{z^k\}$ converges weakly to some element of $Z^*_\lambda=\{u+\lambda b\mid b\in Bu,\ -b\in Au\}$;
--   2. if $\operatorname{zer}(A+B)=\emptyset$, $\{z^k\}$ is unbounded.
--
--   This is the paper's generalized Douglas–Rachford method: it allows inexact evaluation of both resolvents with summable errors and over- or under-relaxation, and it covers the case where $A+B$ has no zero. With $\alpha_k=\beta_k=0$ and $\rho_k=1$ it is the convergence of classical Douglas–Rachford splitting (Lions and Mercier 1979).
--
--   **Formalization Note** The page writes $\{z^k\},\{u^k\},\{v^k\}\subseteq\mathbb R^n$; this is a printed slip for $\mathcal H$ (the theorem begins "Given a Hilbert space $\mathcal H$" and the proof applies Theorem 3 in $\mathcal H$), corrected here. The resolvents are maps $J$ with $\tfrac1\lambda(x-J(x))\in A(J(x))$ for all $x$ (resp. $B$), unique by Corollary 2.2. The sequence $v$ is indexed by all of $\mathbb N$ and $v^0$ is never used. The relaxation condition is encoded as $\exists\,\rho_1,\rho_2$ with $0<\rho_1\le\rho_k\le\rho_2<2$ for all $k$, which is equivalent to the page and implies $\rho_k\in(0,2)$. $A+B$ is the graph sum. Weak convergence is $\langle z^k,y\rangle\to\langle z^*,y\rangle$ for every $y\in\mathcal H$, and unboundedness is "the range of $k\mapsto z^k$ is not bounded". The theorem claims nothing about $J_{\lambda B}(z^k)$.
-- source:
--   Eckstein and Bertsekas, On the Douglas–Rachford Splitting Method and the Proximal Point Algorithm for Maximal Monotone Operators, MIT LIDS-P-1919 (October 1989), p. 21, Theorem 7

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_DouglasRachfordPPA_GenDR_SplittingOperator
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence

open InnerProductSpace ThreeOpSplitting.Convergence

namespace DouglasRachfordPPA.GenDR
/-- Theorem 7 (generalized Douglas–Rachford splitting): for `lam > 0`, maximal monotone `A`, `B`
with resolvent maps `JA = J_{lam A}`, `JB = J_{lam B}`, sequences satisfying (T1)–(T3) with
summable nonnegative errors `α`, `β` and relaxation factors `0 < inf ρ ≤ sup ρ < 2`:
if `zer(A + B) ≠ ∅` then `z` converges weakly to a point of `Z*_lam`; if `zer(A + B) = ∅`
then `z` is unbounded. `v 0` is unused (the paper indexes `v` from `1`). -/
theorem generalized_douglas_rachford_convergence {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A B : H → Set H) (hA : IsMaximalMonotone A) (hB : IsMaximalMonotone B)
    (lam : ℝ) (hlam : 0 < lam)
    (JA JB : H → H) (hJA : IsResolvent lam A JA) (hJB : IsResolvent lam B JB)
    (z u v : ℕ → H) (α β ρ : ℕ → ℝ)
    (hT1 : ∀ k, ‖u k - JB (z k)‖ ≤ β k)
    (hT2 : ∀ k, ‖v (k + 1) - JA ((2 : ℝ) • u k - z k)‖ ≤ α k)
    (hT3 : ∀ k, z (k + 1) = z k + ρ k • (v (k + 1) - u k))
    (hα_nonneg : ∀ k, 0 ≤ α k) (hβ_nonneg : ∀ k, 0 ≤ β k)
    (hα_sum : Summable α) (hβ_sum : Summable β)
    (hρ : ∃ ρ₁ ρ₂ : ℝ, 0 < ρ₁ ∧ ρ₂ < 2 ∧ ∀ k, ρ₁ ≤ ρ k ∧ ρ k ≤ ρ₂) :
    ((zer (opAdd A B)).Nonempty → ∃ zs ∈ Zstar lam A B, WeakTendsto z zs) ∧
    (zer (opAdd A B) = ∅ → ¬ Bornology.IsBounded (Set.range z)) := by sorry

end DouglasRachfordPPA.GenDR
