-- Prove2me | Theorems.Thm_CannonFloydParry_mk_sigmaGen_zero_eq_mk_sigmaGen_one
-- name    : CannonFloydParry.mk_sigmaGen_zero_eq_mk_sigmaGen_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T10:27:33.631984+00:00
-- url     : https://prove2.me/theorems/c24e06d5-6f81-4f45-bd5e-a4f1427f5b56
-- title:
--   p. 247 — in every proper quotient of $\Sigma$, $s_0$ and $s_1$ have the same image
-- statement:
--   Let $\Sigma$ be the group of permutations of $\mathbf{N}$ with finite support and $s_i$ the transposition of $i$ and $i + 1$. If $N$ is a normal subgroup of $\Sigma$ other than $\{1\}$, then $s_0$ and $s_1$ have the same image in $\Sigma/N$.
--
--   **Formalization Note.** A proper quotient group of $\Sigma$ is read as a quotient $\Sigma/N$ by a nontrivial normal subgroup $N$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 6, p. 247, before Lemma 6.7

import Mathlib
import Definitions.Def_CannonFloydParry_V

namespace CannonFloydParry

theorem mk_sigmaGen_zero_eq_mk_sigmaGen_one (N : Subgroup SigmaPerm) [N.Normal] (hN : N ≠ ⊥) :
    (QuotientGroup.mk (sigmaGen 0) : SigmaPerm ⧸ N) = QuotientGroup.mk (sigmaGen 1) := by
  sorry

end CannonFloydParry
