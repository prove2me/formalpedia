-- Prove2me | Theorems.Thm_CohCarrier_isEis_kernel_pair_of_prime
-- name    : CohCarrier.isEis_kernel_pair_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/108630c2-00d2-5d3a-98fa-2feab254e170
-- title:
--   Ihara's lemma: degeneracy kernel pairs are Eisenstein
-- statement:
--   Let $R$ be a commutative ring, $A$ an $R$-module, $\ell_0$ and $q$ nonzero natural numbers and $N$ a natural number. Assume the four level-comparison data `LevelLE N (N*q) ⊤ ⊤ 1`, `LevelLE N (N*q) ⊤ ⊤ q`, `LevelLE (N*q) (N*q*q) ⊤ ⊤ 1`, `LevelLE (N*q) (N*q*q) ⊤ ⊤ q` (each recording the divisibility of the smaller level by the larger, the divisibility of the quotient of levels by the parameter $d \in \{1,q\}$, and compatibility of the unit subgroups, here both $\top$), that $q$ is prime and does not divide $N$, and that $\ell_0$ is prime and does not divide $Nq$. For a level $M$ write $H^1(M) = \mathrm{Hom}(\Gamma_0(M)^{\mathrm{add}}, A)$, the additive homomorphisms from the additive copy of `GammaH M ⊤` (the full congruence subgroup attached to $M$ inside $\mathrm{SL}(2,\mathbb{Z})$) to $A$; write $i_d^{*}$ for the map `iDeg'` given by precomposition with the level-change homomorphism `iotaDeg` of parameter $d$, and call $F \in H^1(M)$ Eisenstein when `heckeT M ⊤ ℓ₀ A F` equals $((\ell_0 : R) + 1)\cdot F$. The conclusion is a conjunction: (1) for all $g, h \in H^1(N)$ with $i_1^{*}g + i_q^{*}h = 0$ in $H^1(Nq)$, both $g$ and $h$ are Eisenstein; (2) for all $x, z' \in H^1(Nq)$ with $i_1^{*}x + i_q^{*}z' = 0$ in $H^1(Nq^2)$, there exists $w \in H^1(N)$ such that $z' - i_1^{*}w$ and $x + i_q^{*}w$ are Eisenstein in $H^1(Nq)$.
--
--   This is Ihara's lemma in the first-cohomology model with arbitrary coefficients, stated simultaneously for the two steps $N \mid Nq$ and $Nq \mid Nq^2$ of the tower, with no restriction on the prime $q$ and no torsion hypothesis on the coefficients. It is the input to the level-raising constructions, and is cited by the results on corner submodules and on refinements of corner families at level $Nq$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_isEis_kernel_pair_of_prime.lean

import Definitions.Def_CohCarrier_Tower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.isEis_kernel_pair_of_prime
    (R : Type) [CommRing R] (A : Type) [AddCommGroup A] [Module R A] (ℓ₀ : ℕ) [NeZero ℓ₀]
    (N q : ℕ) [NeZero q]
    (h₁ : LevelLE N (N * q) ⊤ ⊤ 1) (hq : LevelLE N (N * q) ⊤ ⊤ q)
    (h₁' : LevelLE (N * q) (N * q * q) ⊤ ⊤ 1) (hq' : LevelLE (N * q) (N * q * q) ⊤ ⊤ q)
    (hqp : q.Prime) (hqN : ¬ q ∣ N)
    (hℓ : ℓ₀.Prime) (hℓNq : ¬ ℓ₀ ∣ N * q) :
    (∀ g h : H1 N ⊤ A,
        iDeg' N (N * q) ⊤ ⊤ 1 A h₁ g + iDeg' N (N * q) ⊤ ⊤ q A hq h = 0 →
          IsEis R A N ⊤ ℓ₀ g ∧ IsEis R A N ⊤ ℓ₀ h) ∧
    (∀ x z' : H1 (N * q) ⊤ A,
        iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 A h₁' x + iDeg' (N * q) (N * q * q) ⊤ ⊤ q A hq' z' = 0 →
          ∃ w : H1 N ⊤ A, IsEis R A (N * q) ⊤ ℓ₀ (z' - iDeg' N (N * q) ⊤ ⊤ 1 A h₁ w) ∧
            IsEis R A (N * q) ⊤ ℓ₀ (x + iDeg' N (N * q) ⊤ ⊤ q A hq w)) := by sorry
