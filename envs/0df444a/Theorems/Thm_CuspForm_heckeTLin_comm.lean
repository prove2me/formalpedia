-- Prove2me | Theorems.Thm_CuspForm_heckeTLin_comm
-- name    : CuspForm.heckeTLin_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/1ccd37ab-7f09-5da6-b86f-6e430c5a535d
-- title:
--   Hecke operators Tₚ, T_q commute on cusp forms
-- statement:
--   Let $N$ be a natural number, $k$ an integer, and let $p$, $q$ be natural numbers that are prime and do not divide $N$ (so that $N \neq 0$). For such data the operator [`CuspForm.heckeTLin`](def/ModularForm_HeckeOperatorForms.html#L69) is the $\mathbb{C}$-linear endomorphism of the space $S_k(\Gamma_0(N))$ of weight-$k$ cusp forms for $\Gamma_0(N)$ which sends a cusp form $f$ to the cusp form whose underlying function on the upper half-plane is $\mathrm{heckeT}\,k\,p\,f = \mathrm{heckeU}\,k\,p\,f + f\mid_k \mathrm{heckeDiagMatrix}\,p$, the weight-$k$ modularity under $\Gamma_0(N)$, holomorphy and vanishing at the cusps of this function being part of the construction, together with additivity and $\mathbb{C}$-homogeneity in $f$. The theorem asserts that the two endomorphisms obtained in this way from $(p, hp, hpN)$ and from $(q, hq, hqN)$ commute, that is, $T_p \circ T_q = T_q \circ T_p$ as linear maps $S_k(\Gamma_0(N)) \to S_k(\Gamma_0(N))$. Nothing is asserted about operators attached to primes dividing $N$.
--
--   This is the pairwise commutativity of the Hecke operators $T_p$ at primes of good level, which allows $\{T_p\}_{p \nmid N}$ to be treated as a commuting family of endomorphisms of $S_k(\Gamma_0(N))$ and hence the Hecke algebra to be viewed as a commutative subalgebra of the endomorphism ring. It is used in the analysis of newforms, for instance in identifying a newform up to scalar as a common eigenvector of the $T_p$ and in computing the simultaneous eigenspaces of the $T_p$ and of their duals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_heckeTLin_comm.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.heckeTLin_comm {N : ℕ} (k : ℤ) {p q : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (hq : q.Prime) (hqN : ¬ q ∣ N) :
    Commute (CuspForm.heckeTLin k hp hpN) (CuspForm.heckeTLin k hq hqN) := by sorry
