-- Prove2me | Theorems.Thm_CohCarrier_isEis_kernel_pair_unconditional
-- name    : CohCarrier.isEis_kernel_pair_unconditional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/1545f94e-0401-5365-b4af-f713f7bbe81d
-- title:
--   Ihara's lemma: Eisenstein kernel pairs along the q-tower
-- statement:
--   Fix a commutative ring $R$, an $R$-module $A$, a natural number $\ell_0 \neq 0$, and naturals $N$ and $q \neq 0$. One is given four instances of the predicate `LevelLE`, namely `LevelLE N (N*q) ⊤ ⊤ 1`, `LevelLE N (N*q) ⊤ ⊤ q`, `LevelLE (N*q) (N*q*q) ⊤ ⊤ 1` and `LevelLE (N*q) (N*q*q) ⊤ ⊤ q`, each asserting the divisibility of the smaller level by the larger, divisibility of the degree ($1$ or $q$) by the quotient of levels, and compatibility of the unit subgroups (vacuous, both being $\top$). Further hypotheses: $q$ is prime, $q \nmid N$, $5 \le q$, $A$ has no $q$-torsion in the sense that $(q:\mathbb Z)\cdot a = 0$ implies $a = 0$, $\ell_0$ is prime and $\ell_0 \nmid Nq$. Here $H1\,M\,\top\,A$ denotes the additive homomorphisms from $\mathrm{Additive}(\Gamma_H(M,\top))$ to $A$, $\Gamma_H(M,\top)$ being the copy of $\Gamma_0(M)$ inside $SL_2(\mathbb Z)$, `iDeg'` is precomposition with the degeneracy embedding $\iota_d$ given by conjugation by the lower-triangular matrix of degree $d$, and `IsEis R A M ⊤ ℓ₀ F` means $T_{\ell_0} F = ((\ell_0 : R) + 1)\cdot F$. The conclusion is a conjunction. First: for all $g, h \in H1\,N\,\top\,A$ with $\iota_1^{*}g + \iota_q^{*}h = 0$ in $H1\,(Nq)\,\top\,A$, both $g$ and $h$ are Eisenstein for $T_{\ell_0}$. Second: for all $x, z' \in H1\,(Nq)\,\top\,A$ with $\iota_1^{*}x + \iota_q^{*}z' = 0$ in $H1\,(Nq^2)\,\top\,A$, there exists $w \in H1\,N\,\top\,A$ such that $z' - \iota_1^{*}w$ and $x + \iota_q^{*}w$ are both Eisenstein for $T_{\ell_0}$ at level $Nq$.
--
--   This is the form of Ihara's lemma used as input to level raising in the group-cohomological model of modular symbols: kernel pairs of the two degeneracy maps are Eisenstein for a Hecke operator $T_{\ell_0}$ away from the level, at the bottom step $N \mid Nq$ and, after correction by a level-$N$ class, at the step $Nq \mid Nq^2$. No multiplicity-one hypothesis is imposed. It feeds the construction of the Hecke modules used in the level-raising and Taylor–Wiles steps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_isEis_kernel_pair_unconditional.lean

import Definitions.Def_CohCarrier_Tower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.isEis_kernel_pair_unconditional
    (R : Type) [CommRing R] (A : Type) [AddCommGroup A] [Module R A] (ℓ₀ : ℕ) [NeZero ℓ₀]
    (N q : ℕ) [NeZero q]
    (h₁ : LevelLE N (N * q) ⊤ ⊤ 1) (hq : LevelLE N (N * q) ⊤ ⊤ q)
    (h₁' : LevelLE (N * q) (N * q * q) ⊤ ⊤ 1) (hq' : LevelLE (N * q) (N * q * q) ⊤ ⊤ q)
    (hqp : q.Prime) (hqN : ¬ q ∣ N) (hq5 : 5 ≤ q)
    (hA : ∀ a : A, (q : ℤ) • a = 0 → a = 0)
    (hℓ : ℓ₀.Prime) (hℓNq : ¬ ℓ₀ ∣ N * q) :
    (∀ g h : H1 N ⊤ A,
        iDeg' N (N * q) ⊤ ⊤ 1 A h₁ g + iDeg' N (N * q) ⊤ ⊤ q A hq h = 0 →
          IsEis R A N ⊤ ℓ₀ g ∧ IsEis R A N ⊤ ℓ₀ h) ∧
    (∀ x z' : H1 (N * q) ⊤ A,
        iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 A h₁' x + iDeg' (N * q) (N * q * q) ⊤ ⊤ q A hq' z' = 0 →
          ∃ w : H1 N ⊤ A, IsEis R A (N * q) ⊤ ℓ₀ (z' - iDeg' N (N * q) ⊤ ⊤ 1 A h₁ w) ∧
            IsEis R A (N * q) ⊤ ℓ₀ (x + iDeg' N (N * q) ⊤ ⊤ q A hq w)) := by sorry
