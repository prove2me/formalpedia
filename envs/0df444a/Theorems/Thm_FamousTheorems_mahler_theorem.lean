-- Prove2me | Theorems.Thm_FamousTheorems_mahler_theorem
-- name    : FamousTheorems.mahler_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:57.598689+00:00
-- url     : https://prove2.me/theorems/687f6496-d41f-4b59-843d-af4729b08e68
-- title:
--   Mahler's theorem
-- statement:
--   **Mahler's theorem.** Let $E$ be a complete ultrametric normed $\mathbb Z_p$-module. Every continuous function $f:\mathbb Z_p\to E$ is the sum of its Mahler series
--   $$f(x)=\sum_{n\ge0}\binom xn\,(\Delta^n f)(0),$$
--   converging uniformly, where $\Delta f(x)=f(x+1)-f(x)$ is the forward difference.
--
--   The binomial polynomials $\binom xn$ thus form an orthonormal basis of the continuous functions on $\mathbb Z_p$. This is the $p$-adic analogue of Weierstrass approximation and a basic tool in $p$-adic analysis, $p$-adic $L$-functions and Iwasawa theory.
--
--   **Formalization note.** Mathlib's `PadicInt.hasSum_mahler`, with convergence in the sup-norm topology on `C(ℤ_[p], E)`. `PadicInt.mahlerTerm a n` is the continuous function $x\mapsto\binom xn a$, and `(fwdDiff 1)^[n] f 0` is $\Delta^n f(0)$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `PadicInt.hasSum_mahler`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem mahler_theorem {p : ℕ} [Fact p.Prime] {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
    [IsUltrametricDist E] [CompleteSpace E] (f : C(ℤ_[p], E)) :
    HasSum (fun n : ℕ => PadicInt.mahlerTerm ((fwdDiff 1)^[n] f 0) n) f := by sorry

end FamousTheorems
