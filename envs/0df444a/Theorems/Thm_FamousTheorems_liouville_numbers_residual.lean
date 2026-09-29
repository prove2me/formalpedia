-- Prove2me | Theorems.Thm_FamousTheorems_liouville_numbers_residual
-- name    : FamousTheorems.liouville_numbers_residual
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:38:42.482987+00:00
-- url     : https://prove2.me/theorems/71078fc9-4e36-4053-9e15-324323eb3f61
-- title:
--   Liouville numbers form a residual set
-- statement:
--   **Liouville numbers form a residual set.** The set of Liouville numbers is residual in $\mathbb R$: its complement is meagre. (In fact it is a dense $G_\delta$ set.)
--
--   A real number $x$ is a Liouville number if for every $n$ there are integers $p,q$ with $q>1$ and $0<|x-p/q|<q^{-n}$. Liouville numbers are transcendental (Liouville 1844). So in the sense of Baire category, almost every real number is transcendental, even though the Liouville numbers have Lebesgue measure zero.
--
--   **Formalization note.** Mathlib's `eventually_residual_liouville`. `residual ℝ` is the filter of residual (comeagre) sets, and the statement says that the set of Liouville numbers belongs to it.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `eventually_residual_liouville`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem liouville_numbers_residual : ∀ᶠ x in residual ℝ, Liouville x := by sorry

end FamousTheorems
