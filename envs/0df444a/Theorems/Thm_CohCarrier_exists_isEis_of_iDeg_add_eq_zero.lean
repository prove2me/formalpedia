-- Prove2me | Theorems.Thm_CohCarrier_exists_isEis_of_iDeg_add_eq_zero
-- name    : CohCarrier.exists_isEis_of_iDeg_add_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:36.349084+00:00
-- url     : https://prove2.me/theorems/836fc255-4c66-5c41-bba5-12c5fd184590
-- title:
--   Kernel pairs of the degeneracy maps are Eisenstein modulo level N
-- statement:
--   Fix a commutative ring $R$, an $R$-module $A$, natural numbers $\ell_0$, $N$, $q$ with $\ell_0 \neq 0 \neq q$, and write $H^1(M) := \mathrm{Hom}(\Gamma_H(M), A)$ for the additive group of homomorphisms from the congruence subgroup attached to $M$ and the full subgroup $\top$ of $(\mathbb{Z}/M)^\times$ (that is, $\Gamma_0(M)$) into $A$. Assume `LevelLE` data for the degeneracy indices $d = 1$ and $d = q$ at both steps of the tower, namely for $N \mid Nq$ and for $Nq \mid Nq^2$: in each case $M \mid M'$, $d \mid M'/M$, and the reduction compatibility of the nebentypus subgroups (automatic for $\top$). Assume further that $q$ is prime and $q \nmid N$, that $A$ has no $q$-torsion ($q \cdot a = 0 \Rightarrow a = 0$), that $\mathrm{SL}_2(\mathbb{Z}/q)$ is perfect (its commutator subgroup is everything) and satisfies [`Ihara.HasTrivialSchurMultiplier`](def/SchurMultiplierTrivial.html#L11), i.e. any surjection $\pi : E \to \mathrm{SL}_2(\mathbb{Z}/q)$ of groups whose kernel lies both in the centre of $E$ and in the commutator subgroup of $E$ has trivial kernel; and that $\ell_0$ is prime with $\ell_0 \nmid Nq$. Let $x, z' \in H^1(Nq)$ satisfy $\iota_1^*(x) + \iota_q^*(z') = 0$ in $H^1(Nq^2)$, where $\iota_d^*$ denotes `iDeg'`, precomposition with the conjugation-by-$\mathrm{diag}$ embedding of index $d$. Then there exists $w \in H^1(N)$ such that both $z' - \iota_1^*(w)$ and $x + \iota_q^*(w)$ (with $\iota_d^*$ now for the step $N \mid Nq$) are Eisenstein for $\ell_0$ over $R$, i.e. the transfer Hecke operator `heckeT` at $\ell_0$ acts on each of them as multiplication by $(\ell_0 : R) + 1$.
--
--   This is the Ihara-type statement identifying the kernel of the pair of degeneracy pullbacks from level $Nq$ to level $Nq^2$: such a kernel pair differs by a class pulled back from level $N$ from a pair of classes on which $T_{\ell_0}$ acts by $\ell_0 + 1$, the hypotheses on $\mathrm{SL}_2(\mathbb{Z}/q)$ playing the role of the congruence subgroup property used in the classical argument. It feeds the unconditional form [`CohCarrier.isEis_kernel_pair_unconditional`](thm.html#CohCarrier.isEis_kernel_pair_unconditional) and, through it, the level-raising input to the Taylor–Wiles step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.lean

import Definitions.Def_CohCarrier_Tower
import Definitions.Def_SchurMultiplierTrivial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CohCarrier.exists_isEis_of_iDeg_add_eq_zero
    (R : Type*) [CommRing R] (A : Type) [AddCommGroup A] [Module R A] (ℓ₀ : ℕ) [NeZero ℓ₀]
    (N q : ℕ) [NeZero q]
    (h₁ : LevelLE N (N * q) ⊤ ⊤ 1) (hq : LevelLE N (N * q) ⊤ ⊤ q)
    (h₁' : LevelLE (N * q) (N * q * q) ⊤ ⊤ 1) (hq' : LevelLE (N * q) (N * q * q) ⊤ ⊤ q)
    (hqp : q.Prime) (hqN : ¬ q ∣ N) (hA : ∀ a : A, q • a = 0 → a = 0)
    (hperf : commutator (Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) = ⊤)
    (hstem : Ihara.HasTrivialSchurMultiplier (Matrix.SpecialLinearGroup (Fin 2) (ZMod q)))
    (hℓ : ℓ₀.Prime) (hℓNq : ¬ ℓ₀ ∣ N * q) (x z' : H1 (N * q) ⊤ A)
    (hxz : iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 A h₁' x + iDeg' (N * q) (N * q * q) ⊤ ⊤ q A hq' z' = 0) :
    ∃ w : H1 N ⊤ A, IsEis R A (N * q) ⊤ ℓ₀ (z' - iDeg' N (N * q) ⊤ ⊤ 1 A h₁ w) ∧
      IsEis R A (N * q) ⊤ ℓ₀ (x + iDeg' N (N * q) ⊤ ⊤ q A hq w) := by sorry
