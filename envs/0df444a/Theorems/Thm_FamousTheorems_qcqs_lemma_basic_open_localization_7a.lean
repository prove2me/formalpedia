-- Prove2me | Theorems.Thm_FamousTheorems_qcqs_lemma_basic_open_localization_7a
-- name    : FamousTheorems.qcqs_lemma_basic_open_localization_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:27:26.398342+00:00
-- url     : https://prove2.me/theorems/9685f7aa-dcb2-41b5-b3a6-1aeee2fa5b4d
-- title:
--   The qcqs lemma: sections over a basic open of a qcqs scheme are a localisation
-- statement:
--   **The qcqs lemma.** Let $X$ be a scheme and $U\subseteq X$ an open subset that is quasi-compact and quasi-separated. For every section $f\in\mathcal O_X(U)$, the restriction map exhibits $\mathcal O_X(D(f))$ as the localization $\mathcal O_X(U)_f$, where $D(f)\subseteq U$ is the open set on which $f$ is invertible.
--
--   For affine $U$ this is part of the construction of the structure sheaf. The quasi-compact quasi-separated case, again named by Vakil, is used to show that pushforwards of quasi-coherent sheaves along qcqs morphisms are quasi-coherent. It is also used to show that the global sections functor on a qcqs scheme behaves well under localization.
--
--   **Formalization note.** Mathlib's `AlgebraicGeometry.isLocalization_basicOpen_of_qcqs`. `X.basicOpen f` is $D(f)$, and `IsLocalization.Away f S` says that $S$ is the localization of $\mathcal O_X(U)$ at the powers of $f$, via the restriction map.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `AlgebraicGeometry.isLocalization_basicOpen_of_qcqs`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open Opposite

theorem qcqs_lemma_basic_open_localization_7a {X : AlgebraicGeometry.Scheme} {U : X.Opens} (hU : IsCompact U.carrier) (hU' : IsQuasiSeparated U.carrier)
    (f : X.presheaf.obj (op U)) : IsLocalization.Away f (X.presheaf.obj (op (X.basicOpen f))) := by sorry

end FamousTheorems
