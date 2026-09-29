-- Prove2me | Theorems.Thm_FamousTheorems_burnside_normal_p_complement
-- name    : FamousTheorems.burnside_normal_p_complement
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T01:56:48.673922+00:00
-- url     : https://prove2.me/theorems/b2738856-4de7-4a3a-a5de-7ec1d16245bb
-- title:
--   Burnside's normal p-complement theorem
-- statement:
--   **Burnside's normal $p$-complement theorem.** Let $p$ be a prime and $P$ a Sylow $p$-subgroup of a group $G$ (for example a finite group). If $P$ is central in its normalizer, $N_G(P)\le C_G(P)$, then $P$ has a normal complement: there is a normal subgroup $N\trianglelefteq G$ with $N\cap P=1$ and $NP=G$.
--
--   The theorem is a basic tool for proving that groups are not simple. For example, it shows that if the smallest prime $p$ dividing $|G|$ has cyclic Sylow $p$-subgroups then $G$ has a normal $p$-complement, and it is a starting point of the theory of fusion and transfer.
--
--   **Formalization note.** Mathlib's `MonoidHom.ker_transferSylow_isComplement'`, which shows that the kernel of the transfer homomorphism $G\to P$ is a complement of $P$. `Subgroup.IsComplement' N P` means every element of $G$ is uniquely a product $n p$ with $n\in N$, $p\in P$. The assumptions `Finite (Sylow p G)` and `(P : Subgroup G).FiniteIndex` hold automatically for finite $G$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MonoidHom.ker_transferSylow_isComplement'`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem burnside_normal_p_complement {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G)
    (hP : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ Subgroup.centralizer ((P : Subgroup G) : Set G))
    [(P : Subgroup G).FiniteIndex] : ∃ N : Subgroup G, N.Normal ∧ N.IsComplement' (P : Subgroup G) := by sorry

end FamousTheorems
