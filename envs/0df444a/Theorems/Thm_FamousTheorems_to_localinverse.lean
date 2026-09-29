-- Prove2me | Theorems.Thm_FamousTheorems_to_localinverse
-- name    : FamousTheorems.to_localinverse
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:40:03.145748+00:00
-- url     : https://prove2.me/theorems/caf0bcd2-1ad5-423e-9401-13386e3fbb8f
-- title:
--   The inverse function theorem
-- statement:
--   **The inverse function theorem.** If $f$ has an invertible strict derivative at a point, then $f$ is a local diffeomorphism there and its local inverse is differentiable with $$(f^{-1})'(f(a)) = \bigl(f'(a)\bigr)^{-1}.$$ Invertibility of the linearisation at a single point propagates to invertibility of the map on a whole neighbourhood — the linear approximation controls the nonlinear behaviour locally. The theorem is the foundation of differential topology: the implicit function theorem, the constant rank theorem, and the fact that level sets of submersions are manifolds are all corollaries. Strictness of the derivative matters, and only local invertibility follows: $z \mapsto e^z$ has invertible derivative everywhere yet is globally far from injective. **Formalization note.** `HasStrictDerivAt` is the strict (uniform in two variables) form of differentiability. The result is Mathlib's `HasStrictDerivAt.to_localInverse`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem to_localinverse :
    ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] [inst_1 : CompleteSpace 𝕜] 
    {f : 𝕜 → 𝕜} {f' a : 𝕜} (hf : HasStrictDerivAt f f' a) (hf' : f' ≠ 0), 
    HasStrictDerivAt (HasStrictDerivAt.localInverse f f' a hf hf') f'⁻¹ (f a) := by sorry

end FamousTheorems
