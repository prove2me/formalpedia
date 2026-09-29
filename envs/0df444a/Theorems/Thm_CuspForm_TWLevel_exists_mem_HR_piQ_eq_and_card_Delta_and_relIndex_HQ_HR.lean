-- Prove2me | Theorems.Thm_CuspForm_TWLevel_exists_mem_HR_piQ_eq_and_card_Delta_and_relIndex_HQ_HR
-- name    : CuspForm.TWLevel.exists_mem_HR_piQ_eq_and_card_Delta_and_relIndex_HQ_HR
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/7664e359-0501-5dcf-ac79-0e942a90ccf4
-- title:
--   π_Q maps Hᵣ onto Δ_Q, with index p^{sum vₚ(qᵢ-1)}
-- statement:
--   Let $N$ and $r$ be non-zero natural numbers with $r$ prime, let $t$ be a natural number and let $qv\colon \{0,\dots,t-1\}\to\mathbb N$ be an injective family of non-zero naturals such that each $q_i := qv(i)$ is prime, divides neither $N$ nor equals $r$, and let $p$ be a prime. Write $L = N\,(\prod_i q_i)\,r$ for `level N r qv`, and $\Delta_Q := \prod_i \mathrm{Multiplicative}(\mathbb Z/p^{v_p(q_i-1)})$ for `Delta qv p`. Suppose given, for each $i$, a surjective group homomorphism $\pi^\Delta_i\colon(\mathbb Z/q_i)^\times\to\mathrm{Multiplicative}(\mathbb Z/p^{v_p(q_i-1)})$. Let $\pi_Q\colon(\mathbb Z/L)^\times\to\Delta_Q$ be the homomorphism whose $i$-th component is $\pi^\Delta_i$ composed with reduction of units from $L$ to $q_i$, let $H_r$ be the kernel of reduction of units from $L$ to $r$, and let $H_Q := H_r\cap\ker\pi_Q$. The conclusion is the conjunction of three assertions: every $\delta\in\Delta_Q$ is $\pi_Q(u)$ for some $u\in H_r$; $\Delta_Q$ has cardinality $p^{\sum_i v_p(q_i-1)}$; and the relative index of $H_Q$ in $H_r$, that is the index of $H_Q\cap H_r$ viewed inside $H_r$, equals $p^{\sum_i v_p(q_i-1)}$.
--
--   This is the elementary group-theoretic input to the Taylor–Wiles construction at an auxiliary level $L = N\,Q\,r$ with $Q=\prod_i q_i$: it identifies $H_r/H_Q$ with the finite abelian $p$-group $\Delta_Q$ acting through diamond operators. It is used in the construction of the $\Delta_Q$-structure on the Hecke module at level $L$, in particular by [`CuspForm.TWLevel.exists_algHom_monoidAlgebra_and_basis_ML_HQ`](thm.html#CuspForm.TWLevel.exists_algHom_monoidAlgebra_and_basis_ML_HQ).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_TWLevel_exists_mem_HR_piQ_eq_and_card_Delta_and_relIndex_HQ_HR.lean

import Definitions.Def_CuspForm_TWLevelHeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open CuspForm.TWLevel

theorem CuspForm.TWLevel.exists_mem_HR_piQ_eq_and_card_Delta_and_relIndex_HQ_HR
    (N r : ℕ) [NeZero N] [NeZero r] (hr : r.Prime)
    {t : ℕ} (qv : Fin t → ℕ) [∀ i, NeZero (qv i)] (hqinj : Function.Injective qv)
    (hq : ∀ i, (qv i).Prime) (hqN : ∀ i, ¬ qv i ∣ N) (hqr : ∀ i, qv i ≠ r)
    (p : ℕ) [Fact p.Prime]
    (πΔ : ∀ i, (ZMod (qv i))ˣ →* Multiplicative (ZMod (p ^ padicValNat p (qv i - 1))))
    (hπΔ : ∀ i, Function.Surjective (πΔ i)) :
    (∀ δ : Delta qv p, ∃ u ∈ HR N r qv, piQ N r qv p πΔ u = δ) ∧
    Nat.card (Delta qv p) = p ^ ∑ i, padicValNat p (qv i - 1) ∧
    (HQ N r qv p πΔ).relIndex (HR N r qv) = p ^ ∑ i, padicValNat p (qv i - 1) := by sorry
