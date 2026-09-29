-- Prove2me | Theorems.Thm_FamousTheorems_luroth_theorem
-- name    : FamousTheorems.luroth_theorem
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:20.404633+00:00
-- url     : https://prove2.me/theorems/d3214820-e2e4-4dec-a11f-0b1b3ffa1aac
-- title:
--   Lüroth's theorem
-- statement:
--   **Lüroth's theorem.** Let $K$ be a field and $E$ an intermediate field $K\subseteq E\subseteq K(X)$ of the rational function field in one variable. Then $E=K(f)$ for some rational function $f\in K(X)$.
--
--   Geometrically, every unirational curve is rational: a curve dominated by the projective line is itself birational to the projective line. Lüroth's theorem is one of the classical results of field theory. Castelnuovo extended it to surfaces over $\mathbb C$, while Clemens–Griffiths and Artin–Mumford showed that it fails for threefolds. The question of rationality versus unirationality has remained a central theme of birational geometry.
--
--   **Formalization note.** Mathlib's `RatFunc.Luroth.eq_adjoin_generator`, which constructs an explicit generator `RatFunc.Luroth.generator E`. The statement here only asserts that some generator exists. `IntermediateField.adjoin K {f}` is $K(f)$. The case $E=K$ is included, with $f$ constant.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `RatFunc.Luroth.eq_adjoin_generator`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem luroth_theorem {K : Type*} [Field K] (E : IntermediateField K (RatFunc K)) :
    ∃ f : RatFunc K, E = IntermediateField.adjoin K {f} := by sorry

end FamousTheorems
