-- Prove2me | Theorems.Thm_CuspForm_heckeULin_comm
-- name    : CuspForm.heckeULin_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/1a0bb677-dd7a-5d47-abbc-26825c474234
-- title:
--   Commutativity of Uₚ and U_q on S_k(Γ₀(N))
-- statement:
--   Let $N$ be a natural number, assumed nonzero, let $k$ be an integer, and let $p,q$ be natural numbers with $p \mid N$ and $q \mid N$. For a divisor $p$ of $N$, [`CuspForm.heckeULin k hpN`](def/ModularForm_HeckeOperatorForms.html#L83) is the $\mathbb{C}$-linear endomorphism of the space `CuspForm (CongruenceSubgroup.Gamma0 N) k` of weight $k$ cusp forms on $\Gamma_0(N)$ that sends $f$ to the cusp form whose underlying function on the upper half plane is $\mathrm{heckeU}\,k\,p\,f = \sum_{j<p} f \mid_k \mathrm{heckeMatrix}\,p\,j$, the slash invariance under $\Gamma_0(N)$, the holomorphy and the vanishing at the cusps of this sum being supplied by the construction; the divisibility proofs are literally arguments of the operators, which is why they occur as binders. The assertion is that these two endomorphisms commute in the ring of $\mathbb{C}$-linear endomorphisms of $S_k(\Gamma_0(N))$, i.e. `Commute (CuspForm.heckeULin k hpN) (CuspForm.heckeULin k hqN)`, so $U_p U_q = U_q U_p$. No primality of $p$ or $q$ is required.
--
--   This is the commutativity of the Hecke operators $U_p$ for primes dividing the level, part of the commutativity of the full Hecke algebra acting on $S_k(\Gamma_0(N))$. It is used in the construction of normalized Hecke eigenforms ([`CuspForm.exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul`](thm.html#CuspForm.exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul), [`CuspForm.exists_normalized_eigenvector`](thm.html#CuspForm.exists_normalized_eigenvector)) and in computing traces of the $U$-operators ([`CuspForm.traceLin_heckeULin`](thm.html#CuspForm.traceLin_heckeULin)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_heckeULin_comm.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.heckeULin_comm {N : ℕ} [NeZero N] (k : ℤ) {p q : ℕ} (hpN : p ∣ N) (hqN : q ∣ N) :
    Commute (CuspForm.heckeULin k hpN) (CuspForm.heckeULin k hqN) := by sorry
