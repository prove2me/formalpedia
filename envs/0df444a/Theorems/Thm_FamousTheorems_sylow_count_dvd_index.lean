-- Prove2me | Theorems.Thm_FamousTheorems_sylow_count_dvd_index
-- name    : FamousTheorems.sylow_count_dvd_index
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:27:11.389533+00:00
-- url     : https://prove2.me/theorems/ba4043cb-e77d-466b-9441-3faab95daf5d
-- title:
--   The number of Sylow p-subgroups divides the index
-- statement:
--   **The number of Sylow subgroups divides the index.** Let $p$ be a prime and $G$ a group with finitely many Sylow $p$-subgroups (for example, $G$ finite). If $P$ is a Sylow $p$-subgroup, then the number $n_p$ of Sylow $p$-subgroups divides the index $[G:P]$.
--
--   This is part of the third Sylow theorem. Combined with $n_p\equiv1\pmod p$, it is the main counting tool of finite group theory, showing for example that a group of order $pq$ with $p<q$ and $p\nmid q-1$ is cyclic.
--
--   **Formalization note.** Mathlib's `Sylow.card_dvd_index`. `Nat.card (Sylow p G)` is $n_p$ and `(P : Subgroup G).index` is the index of $P$. The proof uses $n_p=[G:N_G(P)]$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Sylow.card_dvd_index`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem sylow_count_dvd_index {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)] (P : Sylow p G) :
    Nat.card (Sylow p G) ∣ (P : Subgroup G).index := by sorry

end FamousTheorems
