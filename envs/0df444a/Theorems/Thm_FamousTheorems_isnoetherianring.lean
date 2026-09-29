-- Prove2me | Theorems.Thm_FamousTheorems_isnoetherianring
-- name    : FamousTheorems.isnoetherianring
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:01:30.828676+00:00
-- url     : https://prove2.me/theorems/aba62471-4716-4c88-99e5-b94c0cf3c699
-- title:
--   Hilbert's basis theorem
-- statement:
--   **Hilbert's basis theorem.** If $R$ is Noetherian then so is $R[X]$. Finiteness of ideal generation is inherited by polynomial extensions, and by induction $R[X_1,\dots,X_n]$ is Noetherian over any Noetherian base — in particular over a field or over $\mathbb{Z}$. So every ideal of a polynomial ring in finitely many variables is finitely generated, which is what makes algebraic geometry possible: every affine variety is cut out by finitely many equations, and every descending chain of varieties terminates. Hilbert's 1890 proof was famously non-constructive, prompting Gordan's remark that it was theology rather than mathematics. **Formalization note.** `IsNoetherianRing` is the ascending chain condition on ideals. The result is Mathlib's `Polynomial.isNoetherianRing`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem isnoetherianring :
    ∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsNoetherianRing R], 
    IsNoetherianRing (Polynomial R) := by sorry

end FamousTheorems
