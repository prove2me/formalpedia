-- Prove2me | Theorems.Thm_Diaz_isAlgebraic_two_rpow
-- name    : Diaz.isAlgebraic_two_rpow
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:22:43.65264+00:00
-- url     : https://prove2.me/theorems/4f546609-021e-4c96-9543-997accb92323
-- title:
--   $2^{q}$ is algebraic for every rational $q$
-- statement:
--   For every $q \in \mathbb{Q}$, the real number $2^{q}$ — the real power `Real.rpow` of $2$ at the real coercion of $q$ — is algebraic over $\mathbb{Q}$:
--
--   $$\text{$2^{q}$ is a root of } \ X^{\,d} - 2^{\,n} \in \mathbb{Q}[X], \qquad q = \tfrac{n}{d} \text{ in lowest terms}.$$
--
--   **Why.** Write $q = n/d$ with $d = q.\mathrm{den} > 0$ and $n = q.\mathrm{num}$. Then $(2^{q})^{d} = 2^{qd} = 2^{n}$, so $2^{q}$ annihilates $X^{d} - 2^{n}$, and that polynomial is monic of positive degree, hence non-zero. The formal proof is bookkeeping between `Real.rpow`, natural powers and integer powers.
--
--   **Role.** This is what makes the model a model of the *arithmetic* situation and not merely of the field structure. The model's formal exponential is $\mathrm{Exp}_0(a,b) = 2^{a+b}$, and Diaz's conjecture is about numbers whose exponential is algebraic; if $\mathrm{Exp}_0$ took transcendental values, the configuration it realises would not be the one under discussion. Every value of $\mathrm{Exp}_0$ lies in $2^{\mathbb{Q}}$, and this theorem says $2^{\mathbb{Q}} \subseteq \bar{\mathbb{Q}}$.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Exponential.lean#L53-L67

import Mathlib

open ComplexConjugate

theorem Diaz.isAlgebraic_two_rpow (q : ℚ) : IsAlgebraic ℚ ((2 : ℝ) ^ (q : ℝ)) := by sorry
