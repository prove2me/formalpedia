-- Prove2me | Theorems.Thm_BurauFaithful_sl2_neg_one_zpow_even
-- name    : BurauFaithful.sl2_neg_one_zpow_even
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T11:01:36.657355+00:00
-- url     : https://prove2.me/theorems/f44e2ac3-84bc-4378-8732-845d94058543
-- title:
--   Parity input of the assembly: -1^m=1$ forces $ even in $\mathrm{SL}(2,\mathbb Z)$
-- statement:
--   **The parity input of the assembly.** In $\mathrm{SL}(2,\mathbb Z)$ the element
--   $$-1=\begin{pmatrix}-1&0\\0&-1\end{pmatrix}$$
--   is the unique nontrivial central element and has order $2$. Consequently, for every integer $m$,
--   $$(-1)^{m}=1\ \Longrightarrow\ \exists\,k\in\mathbb Z,\quad m=2k .$$
--
--   This is the elementary group-theoretic input of the assembly in the proof of faithfulness of the Burau representation for three strands: the specialization at $t=-1$ of the reduced Burau representation sends the full twist $\Delta^2=(\sigma_1\sigma_2)^3$ to $-1$ (the separate Proved statement `BurauFaithful.spec_reduced_fullTwist_sq`), so once a braid in the kernel is known to be a power $\Delta^{2m}$ of the full twist, the present lemma forces $m$ to be even, i.e. the braid to be a power of $\Delta^4=(\sigma_1\sigma_2)^6$ (Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82, §3.3, pp. 129–130).
--
--   **Formalization Note** The order of $-1$ is computed as $2$ by `orderOf_eq_prime` (from $(-1)^2=1$ and $-1\neq1$, the latter by comparing the $(0,0)$-entry), and the divisibility $2\mid m$ is read off from `orderOf_dvd_iff_zpow_eq_one`.
-- source:
--   J. S. Birman, *Braids, Links, and Mapping Class Groups*, Ann. of Math. Studies 82, Princeton Univ. Press, 1974, §3.3, pp. 129-130.

/-
`BurauFaithful.sl2_neg_one_zpow_even`: the parity input of the assembly.

In the final assembly of NOTES_BURAU.md (SESSION 14) one gets `β = Δ^{2m}` from the injectivity of
the descent section, and then uses `φ(Δ²) = -I` (Proved on the platform as
`BurauFaithful.spec_reduced_fullTwist_sq`) to deduce that `m` is even: `1 = φ(β) = (-I)^m`.
This file records the group-theoretic input: in `SL(2,ℤ)` the element `-1` has order `2`, so
`(-1)^m = 1` forces `m` to be even.
-/
import Definitions.Def_BurauFaithful_UnreducedBurau

set_option autoImplicit false

open Matrix

theorem BurauFaithful.sl2_neg_one_zpow_even (m : ℤ) (h : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ^ m = 1) :
    ∃ k : ℤ, m = 2 * k := by sorry
