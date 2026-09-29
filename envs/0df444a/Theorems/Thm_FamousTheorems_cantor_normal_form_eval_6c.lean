-- Prove2me | Theorems.Thm_FamousTheorems_cantor_normal_form_eval_6c
-- name    : FamousTheorems.cantor_normal_form_eval_6c
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:46:57.936036+00:00
-- url     : https://prove2.me/theorems/8697cf62-0571-431b-aba7-c54fadab7cec
-- title:
--   The Cantor normal form of ordinals
-- statement:
--   **The Cantor normal form of ordinals.** Let $b$ and $o$ be ordinals. Mathlib's Cantor normal form of $o$ in base $b$ is a list of pairs $(e_1,c_1),\dots,(e_k,c_k)$, and
--   $$o=b^{e_1}c_1+b^{e_2}c_2+\dots+b^{e_k}c_k.$$
--
--   For $b\ge2$ the exponents are strictly decreasing and the coefficients are nonzero ordinals less than $b$, and this representation is unique. Cantor introduced it in 1897. For $b=\omega$ it is the standard notation for ordinals below $\varepsilon_0$, used in Gentzen's consistency proof and in the proof of Goodstein's theorem.
--
--   **Formalization note.** Mathlib's `Ordinal.CNF.foldr`. `Ordinal.CNF b o` is the list of (exponent, coefficient) pairs, and the statement folds it into $\sum b^{e_i}c_i$ from the right. The identity holds for all $b$ and $o$ (Mathlib uses conventional values in the degenerate bases $b\le1$). The ordering and uniqueness properties are separate Mathlib lemmas and are not part of this statement.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Ordinal.CNF.foldr`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cantor_normal_form_eval_6c (b o : Ordinal) :
    (Ordinal.CNF b o).foldr (fun p r => b ^ p.1 * p.2 + r) 0 = o := by sorry

end FamousTheorems
