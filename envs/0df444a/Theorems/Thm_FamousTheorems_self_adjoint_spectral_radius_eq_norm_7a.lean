-- Prove2me | Theorems.Thm_FamousTheorems_self_adjoint_spectral_radius_eq_norm_7a
-- name    : FamousTheorems.self_adjoint_spectral_radius_eq_norm_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:03.06684+00:00
-- url     : https://prove2.me/theorems/2b4228ef-e81c-445a-8a11-d2e54997bb44
-- title:
--   Spectral radius of a self-adjoint element of a C*-algebra equals its norm
-- statement:
--   **The spectral radius of a self-adjoint element of a C\*-algebra equals its norm.** Let $A$ be a unital C\*-algebra and $a\in A$ with $a^*=a$. Then
--   $$r(a)=\sup\{|\lambda|:\lambda\in\sigma(a)\}=\|a\|.$$
--
--   The C\*-identity gives $\|a^{2^n}\|=\|a\|^{2^n}$ for self-adjoint $a$, and Gelfand's spectral radius formula $r(a)=\lim\|a^n\|^{1/n}$ then gives the result. It shows that the norm of a C\*-algebra is determined by its algebraic structure. It is a key step in the Gelfand–Naimark theorem and in the continuous functional calculus.
--
--   **Formalization note.** Mathlib's `IsSelfAdjoint.spectralRadius_eq_nnnorm`. `spectralRadius ℂ a` takes values in $[0,\infty]$, and the norm is coerced from the non-negative reals into $[0,\infty]$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `IsSelfAdjoint.spectralRadius_eq_nnnorm`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem self_adjoint_spectral_radius_eq_norm_7a {A : Type*} [CStarAlgebra A] {a : A} (ha : IsSelfAdjoint a) : spectralRadius ℂ a = (‖a‖₊ : ENNReal) := by sorry

end FamousTheorems
