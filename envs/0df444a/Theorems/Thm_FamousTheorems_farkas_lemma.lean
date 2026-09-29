-- Prove2me | Theorems.Thm_FamousTheorems_farkas_lemma
-- name    : FamousTheorems.farkas_lemma
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:51.776799+00:00
-- url     : https://prove2.me/theorems/57ec2c24-eadc-43d3-a415-e3b9ad5c559b
-- title:
--   Farkas' lemma (conic form in Hilbert spaces)
-- statement:
--   **Farkas' lemma (conic form).** Let $E,F$ be real Hilbert spaces, $C\subseteq E$ a closed convex cone, $f:E\to F$ a continuous linear map and $b\in F$. Then $b$ lies in the closure of $f(C)$ if and only if
--   $$\langle b,y\rangle\ge0\quad\text{for every } y\in F \text{ with } f^*(y)\in C^*,$$
--   where $f^*$ is the adjoint of $f$ and $C^*=\{z:\langle x,z\rangle\ge0\ \forall x\in C\}$ is the dual cone.
--
--   For $E=\mathbb R^m$, $F=\mathbb R^n$ and $C$ the nonnegative orthant, $f(C)$ is already closed. The statement is then the classical Farkas lemma: exactly one of the systems $Ax=b,\ x\ge0$ and $A^{\mathsf T}y\ge0,\ \langle b,y\rangle<0$ has a solution. It is the theorem of the alternative behind linear programming duality and the Karush–Kuhn–Tucker conditions.
--
--   **Formalization note.** Mathlib's `ProperCone.relative_hyperplane_separation`. A `ProperCone ℝ E` is a closed convex cone, and `C.map f` is the closure of the image $f(C)$. `ProperCone.innerDual` is the dual cone with respect to the inner product, and `ContinuousLinearMap.adjoint f` is the Hilbert-space adjoint.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ProperCone.relative_hyperplane_separation`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem farkas_lemma {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] {C : ProperCone ℝ E}
    {f : E →L[ℝ] F} {b : F} :
    b ∈ C.map f ↔ ∀ y : F, ContinuousLinearMap.adjoint f y ∈ ProperCone.innerDual (C : Set E) →
      0 ≤ inner ℝ b y := by sorry

end FamousTheorems
