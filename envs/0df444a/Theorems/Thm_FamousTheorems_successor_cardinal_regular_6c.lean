-- Prove2me | Theorems.Thm_FamousTheorems_successor_cardinal_regular_6c
-- name    : FamousTheorems.successor_cardinal_regular_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:46:46.363053+00:00
-- url     : https://prove2.me/theorems/8616e48d-1e9a-4988-886a-c8628bb4e685
-- title:
--   Successor cardinals are regular
-- statement:
--   **Successor cardinals are regular.** For every infinite cardinal $\kappa$, the successor cardinal $\kappa^+$ is regular: its cofinality is $\kappa^+$ itself.
--
--   Equivalently, $\kappa^+$ is not a union of fewer than $\kappa^+$ sets each of size less than $\kappa^+$. The proof uses the axiom of choice and Hessenberg's theorem $\kappa\cdot\kappa=\kappa$. Together with the fact that $\aleph_0$ is regular, it shows that all cardinals $\aleph_{n}$ with finite $n$ are regular, whereas $\aleph_\omega$ is singular.
--
--   **Formalization note.** Mathlib's `Cardinal.isRegular_succ`. `Order.succ c` is the least cardinal greater than $c$, and `Cardinal.IsRegular c` means that $\aleph_0\le c$ and $c\le\operatorname{cof}(c)$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Cardinal.isRegular_succ`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem successor_cardinal_regular_6c {c : Cardinal} (hc : Cardinal.aleph0 ≤ c) : (Order.succ c).IsRegular := by sorry

end FamousTheorems
