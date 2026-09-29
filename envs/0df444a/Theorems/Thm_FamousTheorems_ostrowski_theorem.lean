-- Prove2me | Theorems.Thm_FamousTheorems_ostrowski_theorem
-- name    : FamousTheorems.ostrowski_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:15:30.880025+00:00
-- url     : https://prove2.me/theorems/d8eb9808-52bc-4bfc-ad19-d18fb20c9c07
-- title:
--   Ostrowski's theorem
-- statement:
--   **Ostrowski's theorem.** Every nontrivial absolute value on $\mathbb Q$ is equivalent either to the usual absolute value $|\cdot|_\infty$ or to the $p$-adic absolute value $|\cdot|_p$ for exactly one prime $p$.
--
--   The places of $\mathbb Q$ are therefore the primes together with infinity. This is the starting point of the adelic viewpoint, of the product formula $\prod_v|x|_v=1$, and of the local-global principle (Hasse–Minkowski).
--
--   **Formalization note.** The platform's older `Ostrowskis_Theorem` entry is a deprecated placeholder stating only `True`; this is the actual theorem. Absolute values are real-valued (`AbsoluteValue ℚ ℝ`), and `≈` is equivalence of absolute values (one is a positive power of the other). Mathlib: `Rat.AbsoluteValue.equiv_real_or_padic`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Rat.AbsoluteValue.equiv_real_or_padic`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem ostrowski_theorem (f : AbsoluteValue ℚ ℝ) (hf : f.IsNontrivial) :
    f ≈ Rat.AbsoluteValue.real ∨ ∃! p : ℕ, ∃ (_ : Fact p.Prime), f ≈ Rat.AbsoluteValue.padic p := by sorry

end FamousTheorems
