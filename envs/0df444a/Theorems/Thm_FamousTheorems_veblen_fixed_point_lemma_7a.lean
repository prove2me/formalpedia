-- Prove2me | Theorems.Thm_FamousTheorems_veblen_fixed_point_lemma_7a
-- name    : FamousTheorems.veblen_fixed_point_lemma_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:39.846652+00:00
-- url     : https://prove2.me/theorems/3df22d41-3ebb-4b42-9049-20355106e263
-- title:
--   Veblen's fixed-point lemma for normal ordinal functions
-- statement:
--   **Veblen's fixed-point lemma for normal ordinal functions.** Let $f$ be a normal function on the ordinals, that is, strictly increasing and continuous at limit ordinals. Then $f$ has arbitrarily large fixed points: for every ordinal $a$ there is an ordinal $b\ge a$ with $f(b)=b$.
--
--   The fixed point is obtained as $\sup\{a,f(a),f(f(a)),\dots\}$. Veblen proved the lemma in 1908, and it is the basis of the Veblen hierarchy of normal functions. It gives the ordinals $\varepsilon_0,\varepsilon_1,\dots$ as fixed points of $\alpha\mapsto\omega^\alpha$ and cardinals $\kappa$ with $\kappa=\aleph_\kappa$, and it is used in ordinal notation systems in proof theory.
--
--   **Formalization note.** Mathlib's `Ordinal.nfp_fp` with `Ordinal.le_nfp`. The fixed point $b$ is Mathlib's `Ordinal.nfp f a`, the supremum of the iterates of $f$ at $a$. `Order.IsNormal f` means that $f$ is strictly monotone and continuous at limits.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Ordinal.nfp_fp`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

universe u

theorem veblen_fixed_point_lemma_7a {f : Ordinal.{u} → Ordinal.{u}} (hf : Order.IsNormal f) (a : Ordinal.{u}) : ∃ b, a ≤ b ∧ f b = b := by sorry

end FamousTheorems
