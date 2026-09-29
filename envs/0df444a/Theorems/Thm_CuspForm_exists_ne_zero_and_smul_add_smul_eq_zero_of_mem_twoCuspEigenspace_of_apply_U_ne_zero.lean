-- Prove2me | Theorems.Thm_CuspForm_exists_ne_zero_and_smul_add_smul_eq_zero_of_mem_twoCuspEigenspace_of_apply_U_ne_zero
-- name    : CuspForm.exists_ne_zero_and_smul_add_smul_eq_zero_of_mem_twoCuspEigenspace_of_apply_U_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/103f5e40-301b-5d65-afcc-cad9202553f3
-- title:
--   Multiplicity one for ordinary two-cusp eigenspaces mod π
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ and $p^{2} \nmid M$, and let $H \le (\mathbb{Z}/M)^{\times}$ be a subgroup such that every unit $u$ of $\mathbb{Z}/M$ whose image under the reduction $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$ is $1$ lies in $H$. Let $A \subseteq \mathbb{C}$ be a subring and $\pi \in A$ an element whose principal ideal $(\pi)$ is maximal and contains $p$; write $\kappa = A/(\pi)$. Let $\chi$ assign to each generator in [`CohCarrier.Gen M ∅`](def/CohCarrier_Inst.html#L13) — that is, to each symbol $T_\ell$ with $\ell$ prime and $\ell \nmid M$, each $U_q$ with $q$ prime and $q \mid M$, and each diamond symbol $\langle d\rangle$ with $d \in (\mathbb{Z}/M)^{\times}$ — an element of $\kappa$, and assume $\chi$ is nonzero on the generator $U_p$. Let $\omega_1, \omega_2$ be two elements of [`CuspForm.TwoCuspForms M H 2 p A (Ideal.span {π})`](def/CuspForm_TwoCuspLattice.html#L133), the quotient of the $A$-submodule of weight-two cusp forms on `GammaH M H` spanned by [`CuspForm.twoCuspIntegralSet M H 2 p A`](def/CuspForm_TwoCuspLattice.html#L54) by $(\pi)$ times the whole submodule, and assume both lie in the simultaneous eigenspace [`CuspForm.twoCuspEigenspace`](def/CuspForm_TwoCuspLattice.html#L210), i.e. for every generator $g$ the induced $\kappa$-linear operator [`CuspForm.twoCuspGenMod`](def/CuspForm_TwoCuspLattice.html#L200) attached to $g$ acts on each $\omega_i$ as multiplication by $\chi(g)$. The conclusion is that there is a pair $c = (c_1,c_2) \in \kappa \times \kappa$ with $c \ne 0$ and $c_1 \cdot \omega_1 + c_2 \cdot \omega_2 = 0$; that is, the eigenspace contains no two $\kappa$-linearly independent elements.
--
--   This is the upper-bound half ($\dim_\kappa \le 1$) of the multiplicity-one statement for ordinary Hecke eigenspaces in the mod-$\pi$ reduction of the lattice of weight-two cusp forms integral at both cusps, at a level exactly divisible by $p$ (Wiles, Lemma 2.2), phrased as the assertion that any two eigenvectors with the same eigenvalue system are linearly dependent. It is used in the analysis of the $p$-adic Tate module of the Jacobian of the modular curve at an ordinary, non-Eisenstein maximal ideal, where a one-dimensional multiplicative part has to be produced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_ne_zero_and_smul_add_smul_eq_zero_of_mem_twoCuspEigenspace_of_apply_U_ne_zero.lean

import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.exists_ne_zero_and_smul_add_smul_eq_zero_of_mem_twoCuspEigenspace_of_apply_U_ne_zero
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (A : Subring ℂ) (π : A) (hmax : (Ideal.span ({π} : Set A)).IsMaximal)
    (hp : (p : A) ∈ Ideal.span ({π} : Set A))
    (χ : CohCarrier.Gen M (∅ : Set ℕ) → A ⧸ Ideal.span ({π} : Set A))
    (hord : χ (CohCarrier.Gen.U p Fact.out hpM) ≠ 0)
    (ω₁ ω₂ : CuspForm.TwoCuspForms M H 2 p A (Ideal.span ({π} : Set A)))
    (h₁ : ω₁ ∈ CuspForm.twoCuspEigenspace (Ideal.span ({π} : Set A)) ∅ χ)
    (h₂ : ω₂ ∈ CuspForm.twoCuspEigenspace (Ideal.span ({π} : Set A)) ∅ χ) :
    ∃ c : (A ⧸ Ideal.span ({π} : Set A)) × (A ⧸ Ideal.span ({π} : Set A)),
      c ≠ 0 ∧ c.1 • ω₁ + c.2 • ω₂ = 0 := by sorry
